// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.

//! Binds the extension receiver independently of the dispatch receiver. Only
//! emit a property read when Kotlin metadata and the invoked JVM member agree.

use std::{
    cell::{OnceCell, RefCell},
    collections::HashMap,
    rc::Rc,
};

use crate::{
    classfile::ExceptionHandler,
    context::ClassGroup,
    kotlin::{
        ClassKind, Classifier, Declaration, Function, MemberKind, TypeArgument, Variance,
        Visibility, names::default_descriptor, read_metadata,
    },
};

use super::{
    Bytecode, Constant, Expected, Expr, ExprKind, Instruction, JvmMethodSignature, JvmType,
    KotlinError, Locals, Member, MethodDescriptor, Operand, Primitive, Property, STATIC,
    StackValue, Type, ValueParameter, identifier, load_opcode, logic,
};

#[derive(Debug)]
pub(super) struct Value {
    ty: Type,
    pub(super) jvm: JvmType,
}

impl Value {
    pub(super) fn accepts(&self, expected: Expected<'_>) -> bool {
        load_opcode(&self.jvm) == expected.load()
            && !matches!(expected, Expected::Type(_, jvm) if *jvm != self.jvm)
            && expected.accepts(&self.ty)
    }

    pub(super) fn primitive(&self) -> Option<Primitive> {
        match self.jvm {
            JvmType::Primitive(primitive) => Some(primitive),
            _ => None,
        }
    }
}

#[derive(Debug)]
pub(super) enum Receiver {
    Primitive(Primitive),
    Reference(Rc<Value>),
}

impl Receiver {
    pub(super) fn accepts(&self, expected: Expected<'_>) -> bool {
        match self {
            Self::Primitive(primitive) => expected.primitive() == Some(*primitive),
            Self::Reference(value) => value.accepts(expected),
        }
    }

    pub(super) fn load_opcode(&self) -> u8 {
        match self {
            Self::Primitive(primitive) => load_opcode(&JvmType::Primitive(*primitive)),
            Self::Reference(value) => load_opcode(&value.jvm),
        }
    }

    pub(super) fn primitive(&self) -> Option<Primitive> {
        match self {
            Self::Primitive(primitive) => Some(*primitive),
            Self::Reference(_) => None,
        }
    }
}

#[derive(Default)]
struct Links {
    owners: HashMap<String, Vec<Property>>,
    sites: HashMap<u16, Rc<Getter>>,
}

pub(in crate::kotlin) struct Context<'a> {
    slot: u16,
    ty: &'a Type,
    jvm: &'a JvmType,
    parameters: &'a [ValueParameter],
    assertions: bool,
    receiver: OnceCell<Rc<Value>>,
    group: Option<&'a ClassGroup<'a>>,
    links: RefCell<Links>,
}

impl<'a> Context<'a> {
    pub(in crate::kotlin) fn new(
        function: &'a Function,
        signature: &'a JvmMethodSignature,
        member: &Member<'_>,
        group: Option<&'a ClassGroup<'a>>,
    ) -> Result<Option<Self>, KotlinError> {
        let Some(ty) = &function.receiver else { return Ok(None); };
        let descriptor = &signature.descriptor;
        let Some((jvm, parameters)) = descriptor.parameters.split_first() else {
            return Err(invalid(&function.name));
        };
        let access = match function.flags.visibility()? {
            Visibility::Public | Visibility::Internal => 0x0001,
            Visibility::Private | Visibility::PrivateToThis => 0x0002,
            Visibility::Protected => 0x0004,
            Visibility::Local => return Err(invalid(&function.name)),
        };
        if member.access_flags & 0x0007 != access
            || signature.name != function.name
            || !exact_type(ty, jvm, false)
            || parameters.len() != function.parameters.len()
            || function.parameters.iter().zip(parameters).any(|(param, jvm)| {
                !exact_type(&param.ty, jvm, false)
            })
            || !exact_type(&function.returns, &descriptor.return_type, false)
        {
            return Err(invalid(&function.name));
        }
        Ok(Some(Self {
            slot: u16::from(member.access_flags & STATIC == 0),
            ty,
            jvm,
            parameters: &function.parameters,
            assertions: access != 0x0002,
            receiver: OnceCell::new(),
            group,
            links: RefCell::new(Links::default()),
        }))
    }

    pub(super) fn slots(&self) -> u16 {
        self.jvm.slots()
    }

    pub(super) fn load<'b>(&self, opcode: u8, slot: u16) -> Option<ExprKind<'b>> {
        (slot == self.slot && opcode == load_opcode(self.jvm)).then(|| {
            ExprKind::ExtensionReceiver(match self.jvm {
                JvmType::Primitive(primitive) => Receiver::Primitive(*primitive),
                _ => Receiver::Reference(Rc::clone(self.receiver.get_or_init(|| {
                    Rc::new(Value { ty: self.ty.clone(), jvm: self.jvm.clone() })
                }))),
            })
        })
    }

    pub(super) fn parameter_checks<'b>(
        &self,
        bytecode: &Bytecode<'_, '_>,
        mut instructions: &'b [Instruction],
        locals: &Locals<'_>,
        exceptions: &[ExceptionHandler],
        declaration: &str,
    ) -> Result<&'b [Instruction], KotlinError> {
        // Rendering the non-null declarations regenerates these assertions.
        // Require their exact labels and order; do not drop equivalent-looking
        // assertions that throw differently, or invent guards on unchecked input.
        let original = instructions;
        if self.assertions {
            if !self.ty.nullable && load_opcode(self.jvm) == 0x19 {
                instructions = assertion(bytecode, instructions, self.slot, "<this>", declaration)?;
            }
            for ((slot, jvm), parameter) in locals.slots.iter().zip(self.parameters) {
                if !parameter.ty.nullable && load_opcode(jvm) == 0x19 {
                    instructions = assertion(bytecode, instructions, *slot, &parameter.name, declaration)?;
                }
            }
        }
        let guards = original.len() - instructions.len();
        if guards != 0 {
            let last = &original[guards - 1];
            let end = last.offset + last.len;
            if exceptions.iter().any(|handler| {
                u32::from(handler.start_pc) < end || u32::from(handler.handler_pc) < end
            }) || instructions.iter().any(|instruction| match &instruction.operand {
                Operand::Branch(target) => *target < end,
                Operand::Switch { default, cases } => {
                    *default < end || cases.iter().any(|&(_, target)| target < end)
                }
                _ => false,
            }) {
                return Err(KotlinError::unsupported(declaration, "control flow through an extension null guard"));
            }
        }
        Ok(instructions)
    }

    pub(super) fn getter<'b>(
        &self,
        bytecode: &Bytecode<'b, '_>,
        instruction: &Instruction,
        locals: &Locals<'_>,
        stack: &mut Vec<StackValue<'b>>,
        declaration: &str,
    ) -> Result<Option<Expr<'b>>, KotlinError> {
        let (index, interface) = match (instruction.opcode, &instruction.operand) {
            (0xb6, Operand::Constant(index)) => (*index, false),
            (0xb9, Operand::InvokeInterface { index, count: 1 }) => (*index, true),
            _ => return Ok(None),
        };
        let (subject, subject_jvm) = match stack.last() {
            Some(StackValue::Value(Expr { kind: ExprKind::ExtensionReceiver(Receiver::Reference(receiver)), .. }))
                if !receiver.ty.nullable => (Subject::Receiver, &receiver.jvm),
            Some(StackValue::Value(Expr { kind: ExprKind::Parameter { index, .. }, .. }))
                if !self.parameters[*index].ty.nullable =>
                    (Subject::Parameter(*index), locals.slots[*index].1),
            _ => return Ok(None),
        };
        let JvmType::Object(subject_jvm) = subject_jvm else { return Ok(None); };
        let pool = &bytecode.class.pool;
        if !matches!((pool.get(index)?, interface),
            (Constant::Methodref { .. }, false) | (Constant::InterfaceMethodref { .. }, true))
        {
            return Ok(None);
        }
        let (owner, name, raw) = pool.member_ref(index)?;
        if owner != subject_jvm || !raw.starts_with("()") {
            return Ok(None);
        }
        let mut links = self.links.borrow_mut();
        let linked = if let Some(getter) = links.sites.get(&index) {
            Rc::clone(getter)
        } else {
            let descriptor = MethodDescriptor::parse(raw)?;
            let getter = if owner == bytecode.owner {
                prove_getter(bytecode, interface, locals.templates.properties, name, &descriptor, raw)?
            } else {
                let Some(class) = self.group.and_then(|group| group.get(owner)) else {
                    return Ok(None);
                };
                if !links.owners.contains_key(owner) {
                    let Some(metadata) = read_metadata(class)? else { return Ok(None); };
                    let Declaration::Class(declaration) = metadata.declaration else { return Ok(None); };
                    if declaration.name.local || !same_class(&declaration.name.id, owner)
                        || (declaration.kind == ClassKind::Interface) != interface
                    {
                        return Ok(None);
                    }
                    links.owners.insert(owner.to_owned(), declaration.members.properties);
                }
                let target = Bytecode { class, owner };
                prove_getter(&target, interface, &links.owners[owner], name, &descriptor, raw)?
            };
            let Some(property) = getter else { return Ok(None); };
            let getter = Rc::new(Getter {
                name: property.name.clone(),
                value: Value { ty: property.ty.clone(), jvm: descriptor.return_type },
            });
            links.sites.insert(index, Rc::clone(&getter));
            getter
        };
        stack.pop();
        Ok(Some(Expr::new(ExprKind::BoundGetter(Read { subject, getter: linked }), 2, declaration)?))
    }
}

fn assertion<'a>(
    bytecode: &Bytecode<'_, '_>,
    instructions: &'a [Instruction],
    slot: u16,
    label: &str,
    declaration: &str,
) -> Result<&'a [Instruction], KotlinError> {
    if let Some((actual, name, rest)) = bytecode.null_check(instructions)?
        && actual == slot && name == label
        && matches!(instructions[2].operand, Operand::Constant(index)
            if matches!(bytecode.class.pool.get(index)?, Constant::Methodref { .. }))
        && bytecode.reference(&instructions[2], 0xb8)? == Some((
            "kotlin/jvm/internal/Intrinsics", "checkNotNullParameter",
            "(Ljava/lang/Object;Ljava/lang/String;)V",
        ))
    {
        return Ok(rest);
    }
    Err(KotlinError::unsupported(declaration, "unproven Kotlin extension parameter null guard"))
}

fn prove_getter<'a>(
    bytecode: &Bytecode<'_, '_>,
    interface: bool,
    properties: &'a [Property],
    name: &str,
    descriptor: &MethodDescriptor,
    raw: &str,
) -> Result<Option<&'a Property>, KotlinError> {
    if (bytecode.class.access_flags & 0x0200 != 0) != interface
        || descriptor.return_type == JvmType::Void
    {
        return Ok(None);
    }
    let mut candidates = properties.iter().filter(|property| {
        property.signature.getter.as_ref().is_some_and(|getter| {
            getter.name == name && getter.descriptor == *descriptor
        })
    });
    let Some(property) = candidates.next() else { return Ok(None); };
    if candidates.next().is_some()
        || property.receiver.is_some()
        || !property.type_parameters.is_empty()
        || !property.context_receivers.is_empty()
        || !property.context_parameters.is_empty()
        || property.flags.member_kind() != MemberKind::Declaration
        || property.flags.visibility()? != Visibility::Public
        || property.getter_flags.unwrap_or(property.flags).visibility()? != Visibility::Public
        || property.getter_flags.is_some_and(|flags| flags.has(8))
        || !exact_type(&property.ty, &descriptor.return_type, false)
        || properties.iter().any(|other| other.name == property.name && !std::ptr::eq(other, property))
    {
        return Ok(None);
    }
    let pool = &bytecode.class.pool;
    let mut found = false;
    for method in &bytecode.class.methods {
        if pool.utf8(method.name_index)? == name && pool.utf8(method.descriptor_index)? == raw {
            if found || method.access_flags & (0x0007 | STATIC | 0x0040 | 0x1000) != 0x0001 {
                return Ok(None);
            }
            found = true;
        }
    }
    Ok(found.then_some(property))
}

#[derive(Debug)]
enum Subject {
    Receiver,
    Parameter(usize),
}

#[derive(Debug)]
struct Getter {
    name: String,
    value: Value,
}

#[derive(Debug)]
pub(super) struct Read {
    subject: Subject,
    getter: Rc<Getter>,
}

impl Read {
    pub(super) fn value(&self) -> &Value {
        &self.getter.value
    }

    pub(super) fn write(
        &self,
        out: &mut String,
        parameters: &[ValueParameter],
        declaration: &str,
    ) -> Result<(), KotlinError> {
        match self.subject {
            Subject::Receiver => out.push_str("this"),
            Subject::Parameter(index) => identifier(out, &parameters[index].name, declaration)?,
        }
        out.push('.');
        identifier(out, &self.getter.name, declaration)
    }
}

fn invalid(declaration: &str) -> KotlinError {
    KotlinError::unsupported(declaration, "unproven Kotlin extension JVM signature")
}

fn same_class(id: &str, owner: &str) -> bool {
    !id.contains('$')
        && id.bytes().map(|byte| if byte == b'.' { b'$' } else { byte }).eq(owner.bytes())
}

fn exact_type(ty: &Type, jvm: &JvmType, boxed: bool) -> bool {
    let Classifier::Class(name) = &ty.classifier else { return false; };
    if name.local || ty.raw || ty.flexible.is_some() || ty.suspend {
        return false;
    }
    match jvm {
        JvmType::Void => name.id == "kotlin/Unit" && !ty.nullable,
        JvmType::Primitive(primitive) => !boxed && logic::primitive_type(ty) == Some(*primitive),
        JvmType::Object(owner) => {
            if !name.id.starts_with("kotlin/") {
                return same_class(&name.id, owner);
            }
            if name.id == "kotlin/Unit" {
                return owner == "kotlin/Unit";
            }
            if boxed || ty.nullable {
                let wrapper = match name.id.as_str() {
                    "kotlin/Boolean" => "java/lang/Boolean",
                    "kotlin/Byte" => "java/lang/Byte",
                    "kotlin/Char" => "java/lang/Character",
                    "kotlin/Short" => "java/lang/Short",
                    "kotlin/Int" => "java/lang/Integer",
                    "kotlin/Long" => "java/lang/Long",
                    "kotlin/Float" => "java/lang/Float",
                    "kotlin/Double" => "java/lang/Double",
                    _ => "",
                };
                if owner == wrapper {
                    return true;
                }
            }
            default_descriptor(ty).is_some_and(|raw| {
                raw.strip_prefix('L').and_then(|raw| raw.strip_suffix(';')) == Some(owner)
            })
        }
        JvmType::Array(component) if name.id == "kotlin/Array" => match ty.arguments.as_slice() {
            [TypeArgument::Type(Variance::Invariant | Variance::Out, element)] => {
                exact_type(element, component, true)
            }
            [TypeArgument::Star] => matches!(component.as_ref(), JvmType::Object(name) if name == "java/lang/Object"),
            _ => false,
        },
        JvmType::Array(component) => {
            default_descriptor(ty).is_some_and(|raw| {
                matches!((raw.as_ref(), component.as_ref()),
                    ("[Z", JvmType::Primitive(Primitive::Boolean))
                        | ("[B", JvmType::Primitive(Primitive::Byte))
                        | ("[C", JvmType::Primitive(Primitive::Char))
                        | ("[S", JvmType::Primitive(Primitive::Short))
                        | ("[I", JvmType::Primitive(Primitive::Int))
                        | ("[J", JvmType::Primitive(Primitive::Long))
                        | ("[F", JvmType::Primitive(Primitive::Float))
                        | ("[D", JvmType::Primitive(Primitive::Double)))
            })
        }
    }
}
