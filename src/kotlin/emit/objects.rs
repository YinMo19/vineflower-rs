// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.

use std::{borrow::Cow, cell::RefCell, ops::Range};

use crate::{
    bytecode::{Instruction, Operand},
    classfile::{Constant, find_attribute},
    kotlin::{
        JvmFieldSignature, Type,
        body::{Assignment, CONSTRUCTOR_MARKER, ConstructorCall, load_opcode, local_load, local_store, return_opcode},
    },
};

use super::{
    Bytecode, ClassDeclaration, ClassKind, Expr, FINAL, JvmMethodSignature, JvmType, KotlinError,
    Member, STATIC, ValueParameter, Visibility, body, error,
};

const SYNTHETIC: u16 = 0x1000;
const PUBLIC: u16 = 0x0001;
const PRIVATE: u16 = 0x0002;
const JVM_STATIC: &str = "Lkotlin/jvm/JvmStatic;";

pub(super) struct Singleton<'a, 'data> {
    pub storage: Bytecode<'a, 'data>,
    pub body: Bytecode<'a, 'data>,
    pub instance: &'a Member<'data>,
    instance_ref: (&'a str, &'a str, &'a str),
    code: Vec<Instruction>,
    first_assignment: usize,
    host_methods: RefCell<Vec<&'a Member<'data>>>,
}

pub(super) enum Initializer<'a> {
    Expression(Expr<'a>),
    Regex(Cow<'a, [u16]>),
}

impl Initializer<'_> {
    pub fn parameter(&self, descriptor: &JvmType) -> Option<usize> {
        match self {
            Self::Expression(expr) => expr.parameter(descriptor),
            Self::Regex(_) => None,
        }
    }

    pub fn write(&self, out: &mut String, ty: &Type, descriptor: &JvmType,
        parameters: &[ValueParameter], declaration: &str,
    ) -> Result<(), KotlinError> {
        match self {
            Self::Expression(expr) => expr.write(out, ty, descriptor, parameters, declaration),
            Self::Regex(value) if ty.class_id() == Some("kotlin/text/Regex")
                && matches!(descriptor, JvmType::Object(name) if name == "kotlin/text/Regex") =>
            {
                out.push_str("kotlin.text.Regex(");
                body::write_string(out, value.iter().copied());
                out.push(')');
                Ok(())
            }
            Self::Regex(_) => Err(error(declaration, "Regex initializer does not match the Kotlin property")),
        }
    }
}

pub(super) struct Initialization<'a> {
    pub field: &'a str,
    pub descriptor: &'a str,
    pub value: Initializer<'a>,
    pub rhs_offsets: Option<Range<u32>>,
}

impl<'a> From<Assignment<'a>> for Initialization<'a> {
    fn from(assignment: Assignment<'a>) -> Self {
        Self {
            field: assignment.field,
            descriptor: assignment.descriptor,
            value: Initializer::Expression(assignment.value),
            rhs_offsets: assignment.rhs_offsets,
        }
    }
}

impl<'a, 'data> Singleton<'a, 'data> {
    pub fn validate(
        body: &Bytecode<'a, 'data>,
        declaration: &ClassDeclaration,
        constructor_call: ConstructorCall<'_>,
        host: Option<(&Bytecode<'a, 'data>, &str)>,
    ) -> Result<Self, KotlinError> {
        let invalid = || error(body.owner, "Kotlin singleton constructor or allocation shell");
        let companion = declaration.kind == ClassKind::CompanionObject;
        if companion != host.is_some() || body.class.access_flags & FINAL == 0 {
            return Err(invalid());
        }
        let [ctor] = declaration.constructors.as_slice() else { return Err(invalid()); };
        let sig = ctor.signature.as_ref().ok_or_else(invalid)?;
        if ctor.flags.has(4) || ctor.flags.has_annotations() || ctor.flags.visibility()? != Visibility::Private
            || !ctor.parameters.is_empty() || sig.name != "<init>" || !sig.descriptor.parameters.is_empty()
            || sig.descriptor.return_type != JvmType::Void
        {
            return Err(invalid());
        }
        let method = body.find_method(sig)?.ok_or_else(invalid)?;
        if method.access_flags != PRIVATE || !body.has_empty_constructor_body(method, constructor_call)?
        {
            return Err(invalid());
        }
        if companion {
            let marked = raw_method(body, "<init>", CONSTRUCTOR_MARKER)?.ok_or_else(invalid)?;
            if !body.class.fields.is_empty() || raw_method(body, "<clinit>", "()V")?.is_some()
                || marked.access_flags != PUBLIC | SYNTHETIC
                || !body.has_empty_constructor_body(marked, ConstructorCall::Direct(body.owner))?
            {
                return Err(invalid());
            }
        }
        let (storage, instance_name) = host.unwrap_or((body, "INSTANCE"));
        let pool = &storage.class.pool;
        let mut instance = None;
        for field in &storage.class.fields {
            let name = pool.utf8(field.name_index)?;
            if name != instance_name {
                continue;
            }
            let raw = pool.utf8(field.descriptor_index)?;
            if instance.is_some() || field.access_flags != PUBLIC | STATIC | FINAL
                || raw.strip_prefix('L').and_then(|name| name.strip_suffix(';')) != Some(body.owner)
                || find_attribute(&field.attributes, pool, "ConstantValue")?.is_some()
            {
                return Err(invalid());
            }
            instance = Some((field, name, raw));
        }
        let (instance, instance_name, instance_descriptor) = instance.ok_or_else(invalid)?;
        let instance_ref = (storage.owner, instance_name, instance_descriptor);
        let clinit = raw_method(storage, "<clinit>", "()V")?.ok_or_else(invalid)?;
        let code = storage.instructions(clinit, storage.owner)?;
        let first_assignment = if companion { 5 } else { 4 };
        let Some(prefix) = code.get(..first_assignment) else { return Err(invalid()); };
        let [new, dup, tail @ ..] = prefix else { unreachable!() };
        let (init, put, constructor_descriptor) = match tail {
            [null, init, put] if companion && null.opcode == 0x01 => (init, put, CONSTRUCTOR_MARKER),
            [init, put] if !companion => (init, put, "()V"),
            _ => return Err(invalid()),
        };
        let Operand::Constant(index) = new.operand else { return Err(invalid()); };
        if clinit.access_flags != STATIC || new.opcode != 0xbb || pool.class_name(index)? != body.owner
            || dup.opcode != 0x59 || storage.reference(init, 0xb7)? != Some((body.owner, "<init>", constructor_descriptor))
            || storage.reference(put, 0xb3)? != Some(instance_ref)
            || !code.last().is_some_and(|ret| ret.opcode == 0xb1) || first_assignment >= code.len()
        {
            return Err(invalid());
        }
        Ok(Self {
            storage: Bytecode { class: storage.class, owner: storage.owner },
            body: Bytecode { class: body.class, owner: body.owner },
            instance, instance_ref, code, first_assignment,
            host_methods: RefCell::new(Vec::new()),
        })
    }

    pub fn is_companion(&self) -> bool {
        self.storage.owner != self.body.owner
    }

    pub fn assignments(&self) -> Result<Vec<Initialization<'a>>, KotlinError> {
        let code = &self.code[self.first_assignment..self.code.len() - 1];
        let mut first = 0;
        let mut index = 0;
        let mut assignments = Vec::new();
        while index < code.len() {
            let instruction = &code[index];
            if instruction.opcode == 0xbb {
                let valid = self.regex(&code[index..])?.ok_or_else(|| error(self.body.owner, "unproven singleton property allocation"))?;
                assignments.extend(self.storage.static_assignments(&code[first..index], self.body.owner)?.into_iter().map(Initialization::from));
                assignments.push(valid);
                index += 5;
                first = index;
            } else {
                index += 1;
            }
        }
        assignments.extend(self.storage.static_assignments(&code[first..], self.body.owner)?.into_iter().map(Initialization::from));
        Ok(assignments)
    }

    fn regex(&self, code: &[Instruction]) -> Result<Option<Initialization<'a>>, KotlinError> {
        let [new, dup, constant, init, put, ..] = code else { return Ok(None); };
        let (Operand::Constant(class), Operand::Constant(string)) = (&new.operand, &constant.operand) else { return Ok(None); };
        let pool = &self.storage.class.pool;
        if pool.class_name(*class)? != "kotlin/text/Regex" || dup.opcode != 0x59
            || !matches!(constant.opcode, 0x12 | 0x13)
            || self.storage.reference(init, 0xb7)? != Some(("kotlin/text/Regex", "<init>", "(Ljava/lang/String;)V"))
        {
            return Ok(None);
        }
        let Constant::String(string) = *pool.get(*string)? else { return Ok(None); };
        let Some((owner, field, descriptor)) = self.storage.reference(put, 0xb3)? else { return Ok(None); };
        if owner != self.storage.owner || descriptor != "Lkotlin/text/Regex;" {
            return Ok(None);
        }
        Ok(Some(Initialization {
            field,
            descriptor,
            value: Initializer::Regex(pool.utf16(string)?),
            rhs_offsets: None,
        }))
    }

    pub fn function_static(&self, signature: &JvmMethodSignature, metadata_annotation: bool,
        declaration: &str,
    ) -> Result<bool, KotlinError> {
        let member = self.body.find_method(signature)?.ok_or_else(|| error(declaration, "missing singleton JVM method"))?;
        let jvm_static = jvm_static_annotation(&self.body, member, declaration)?;
        if metadata_annotation != jvm_static {
            return Err(error(declaration, "singleton function annotations do not match metadata"));
        }
        if jvm_static && self.is_companion() {
            self.forward(signature, member, declaration)?;
        }
        Ok(jvm_static)
    }

    pub fn property_static(&self, annotation: Option<&JvmMethodSignature>, declaration: &str) -> Result<bool, KotlinError> {
        let Some(signature) = annotation else { return Ok(false); };
        let invalid = || error(declaration, "unproven singleton property annotation");
        let member = self.body.find_method(signature)?.ok_or_else(invalid)?;
        if !signature.name.ends_with("$annotations") || !signature.descriptor.parameters.is_empty()
            || signature.descriptor.return_type != JvmType::Void || member.access_flags != PUBLIC | STATIC | SYNTHETIC
            || !matches!(self.body.instructions(member, declaration)?.as_slice(), [ret] if ret.opcode == 0xb1)
            || !jvm_static_annotation(&self.body, member, declaration)?
        {
            return Err(invalid());
        }
        Ok(true)
    }

    pub fn getter(&self, member: &Member<'data>, signature: &JvmMethodSignature, field: &JvmFieldSignature,
        raw: &str, jvm_static: bool, declaration: &str,
    ) -> Result<(), KotlinError> {
        self.accessor(member, field, raw, false, declaration)?;
        if jvm_static && self.is_companion() { self.forward(signature, member, declaration)?; }
        Ok(())
    }

    pub fn setter(&self, member: &Member<'data>, signature: &JvmMethodSignature, field: &JvmFieldSignature,
        raw: &str, jvm_static: bool, declaration: &str,
    ) -> Result<(), KotlinError> {
        self.accessor(member, field, raw, true, declaration)?;
        if jvm_static && self.is_companion() { self.forward(signature, member, declaration)?; }
        Ok(())
    }

    fn accessor(&self, member: &Member<'data>, field: &JvmFieldSignature, raw: &str, write: bool,
        declaration: &str,
    ) -> Result<(), KotlinError> {
        let invalid = || error(declaration, "unproven singleton property accessor");
        let code = self.body.instructions(member, declaration)?;
        let slot = u16::from(member.access_flags & STATIC == 0);
        let load = load_opcode(&field.descriptor);
        let expected_ret = if write { 0xb1 } else { return_opcode(&field.descriptor) };
        let (access, ret) = match code.as_slice() {
            [get, ret] if !write => (get, ret),
            [value, put, ret] if write && local_load(value) == Some((load, slot)) => (put, ret),
            _ => return Err(invalid()),
        };
        let opcode = if write { 0xb3 } else { 0xb2 };
        let target = (self.storage.owner, field.name.as_str(), raw);
        if ret.opcode != expected_ret { return Err(invalid()); }
        if self.body.reference(access, opcode)? == Some(target) {
            return Ok(());
        }
        let Some((owner, bridge, descriptor)) = self.body.reference(access, 0xb8)? else { return Err(invalid()); };
        let source_descriptor = self.body.class.pool.utf8(member.descriptor_index)?;
        if !self.is_companion() || owner != self.storage.owner || descriptor != source_descriptor
            || !bridge.starts_with("access$") || !bridge.ends_with("$cp")
        {
            return Err(invalid());
        }
        let helper = raw_method(&self.storage, bridge, descriptor)?.ok_or_else(invalid)?;
        let code = self.storage.instructions(helper, declaration)?;
        let (access, ret) = match code.as_slice() {
            [get, ret] if !write => (get, ret),
            [value, put, ret] if write && local_load(value) == Some((load, 0)) => (put, ret),
            _ => return Err(invalid()),
        };
        if helper.access_flags != PUBLIC | STATIC | FINAL | SYNTHETIC || ret.opcode != expected_ret
            || self.storage.reference(access, opcode)? != Some(target)
        {
            return Err(invalid());
        }
        self.host_methods.borrow_mut().push(helper);
        Ok(())
    }

    fn forward(&self, signature: &JvmMethodSignature, member: &Member<'data>, declaration: &str) -> Result<(), KotlinError> {
        let invalid = || error(declaration, "unproven @JvmStatic companion forwarder");
        let raw = self.body.class.pool.utf8(member.descriptor_index)?;
        let bridge = raw_method(&self.storage, &signature.name, raw)?.ok_or_else(invalid)?;
        let code = self.storage.instructions(bridge, declaration)?;
        let [get, args @ .., invoke, ret] = code.as_slice() else { return Err(invalid()); };
        if bridge.access_flags != (member.access_flags & 0x0007) | STATIC | FINAL
            || args.len() != signature.descriptor.parameters.len()
            || self.storage.reference(get, 0xb2)? != Some(self.instance_ref)
            || self.storage.reference(invoke, 0xb6)? != Some((self.body.owner, signature.name.as_str(), raw))
            || ret.opcode != return_opcode(&signature.descriptor.return_type)
        {
            return Err(invalid());
        }
        let mut slot = 0;
        for (load, parameter) in args.iter().zip(&signature.descriptor.parameters) {
            if local_load(load) != Some((load_opcode(parameter), slot)) { return Err(invalid()); }
            slot += parameter.slots();
        }
        self.host_methods.borrow_mut().push(bridge);
        Ok(())
    }

    pub fn verify_host_methods(&self) -> Result<(), KotlinError> {
        if !self.is_companion() { return Ok(()); }
        let methods = self.host_methods.borrow();
        for member in &self.storage.class.methods {
            if member.access_flags & STATIC != 0 && !methods.iter().any(|method| std::ptr::eq(*method, member))
                && self.storage.class.pool.utf8(member.name_index)? != "<clinit>"
            {
                return Err(error(self.storage.owner, "unclaimed static method in a Kotlin companion host"));
            }
        }
        Ok(())
    }

    /// Kotlin's postfix update of an own Int backing field. Dropping the
    /// INSTANCE/pop shell is safe only for the proven self-storage layout.
    pub fn int_update(&self, member: &Member<'data>, declaration: &str) -> Result<Option<Update<'a>>, KotlinError> {
        if self.is_companion() { return Ok(None); }
        let code = member.code(&self.body.class.pool)?.ok_or_else(|| error(declaration, "missing singleton JVM code"))?;
        if !code.exceptions.is_empty() { return Ok(None); }
        let instructions = crate::bytecode::decode(code.bytes)?;
        let [read, save, middle @ .., reload, delta, add, put, ret] = instructions.as_slice() else { return Ok(None); };
        let Some((owner, field, "I")) = self.body.reference(read, 0xb2)? else { return Ok(None); };
        let Some((0x36, temp)) = local_store(save) else { return Ok(None); };
        let instance = member.access_flags & STATIC == 0;
        if owner != self.body.owner || temp < u16::from(instance) || local_load(reload) != Some((0x15, temp))
            || self.body.reference(put, 0xb3)? != Some((owner, field, "I")) || ret.opcode != 0xb1
        { return Ok(None); }
        if !middle.is_empty() && !matches!(middle, [get, pop] if !instance && pop.opcode == 0x57
            && self.body.reference(get, 0xb2)? == Some(self.instance_ref))
        { return Ok(None); }
        let increment = match (delta.opcode, add.opcode) {
            (0x04, 0x60) => true,
            (0x02, 0x60) | (0x04, 0x64) => false,
            _ => return Ok(None),
        };
        Ok(Some(Update { field, increment, instructions }))
    }
}

pub(super) struct Update<'a> {
    pub field: &'a str,
    pub increment: bool,
    pub instructions: Vec<Instruction>,
}

fn jvm_static_annotation(bytecode: &Bytecode<'_, '_>, member: &Member<'_>, declaration: &str) -> Result<bool, KotlinError> {
    let mut found = false;
    for visible in [true, false] {
        for annotation in member.annotations(&bytecode.class.pool, visible)? {
            match bytecode.class.pool.utf8(annotation.type_index)? {
                JVM_STATIC if visible && !found && annotation.elements.is_empty() => found = true,
                "Lorg/jetbrains/annotations/NotNull;" | "Lorg/jetbrains/annotations/Nullable;"
                    if !visible && annotation.elements.is_empty() => {}
                _ => return Err(error(declaration, "unsupported singleton declaration annotation")),
            }
        }
    }
    Ok(found)
}

fn raw_method<'a, 'data>(bytecode: &Bytecode<'a, 'data>, name: &str, descriptor: &str) -> Result<Option<&'a Member<'data>>, KotlinError> {
    let pool = &bytecode.class.pool;
    let mut result = None;
    for member in &bytecode.class.methods {
        if pool.utf8(member.name_index)? == name && pool.utf8(member.descriptor_index)? == descriptor {
            if result.replace(member).is_some() {
                return Err(error(bytecode.owner, "duplicate singleton JVM method"));
            }
        }
    }
    Ok(result)
}
