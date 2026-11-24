// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.

//! Bind JVM calls to declarations before lowering their operands. A member
//! extension's dispatch receiver is lexical; its first argument is the source
//! receiver, not an ordinary argument.

use crate::{
    classfile::ClassFile,
    kotlin::{ClassKind, ClassName, Classifier, MemberKind, Visibility},
};

use super::{
    Bytecode, Constant, Expected, Expr, ExprKind, Instruction, JvmType, KotlinError, Literal,
    Locals, MethodDescriptor, Operand, Primitive, STATIC, StackValue, Type, ValueParameter,
    defaults, extensions::{Context, Value, exact_type}, identifier, load_opcode, qualified,
};

#[derive(Clone, Copy)]
pub(super) struct Allocation<'a> {
    owner: &'a str,
    after: u32,
    duplicate: bool,
}

#[derive(Debug)]
pub(super) struct Call<'a> {
    target: Target<'a>,
    arguments: Vec<Argument<'a>>,
    result: Value,
}

#[derive(Debug)]
enum Target<'a> {
    Constructor,
    Member { name: String, receiver: Option<Argument<'a>> },
}

#[derive(Debug)]
struct Argument<'a> {
    value: Expr<'a>,
    ty: Type,
    jvm: JvmType,
    name: Option<String>,
}

impl Call<'_> {
    pub(super) fn result(&self) -> &Value {
        &self.result
    }

    pub(super) fn write(
        &self,
        out: &mut String,
        parameters: &[ValueParameter],
        declaration: &str,
    ) -> Result<(), KotlinError> {
        match &self.target {
            Target::Constructor => qualified(out, self.result.ty.class_id().unwrap(), declaration)?,
            Target::Member { name, receiver } => {
                if let Some(receiver) = receiver {
                    receiver.value.write_at(out, Expected::Type(&receiver.ty, &receiver.jvm), parameters, declaration, u8::MAX)?;
                } else {
                    out.push_str("this");
                }
                out.push('.');
                identifier(out, name, declaration)?;
            }
        }
        out.push('(');
        for (index, argument) in self.arguments.iter().enumerate() {
            if index != 0 {
                out.push_str(", ");
            }
            if let Some(name) = &argument.name {
                identifier(out, name, declaration)?;
                out.push_str(" = ");
            }
            argument.value.write(out, &argument.ty, &argument.jvm, parameters, declaration)?;
        }
        out.push(')');
        Ok(())
    }
}

pub(super) fn lower<'a>(
    bytecode: &Bytecode<'a, '_>,
    instruction: &Instruction,
    context: &Context<'_>,
    locals: &Locals<'_>,
    stack: &mut Vec<StackValue<'a>>,
    declaration: &str,
) -> Result<bool, KotlinError> {
    match (instruction.opcode, &instruction.operand) {
        (0xbb, Operand::Constant(index)) => {
            let owner = bytecode.class.pool.class_name(*index)?;
            stack.push(StackValue::Allocation(Allocation {
                owner,
                after: instruction.offset + instruction.len,
                duplicate: false,
            }));
        }
        (0x59, _) => {
            let Some(StackValue::Allocation(allocation)) = stack.last() else { return Ok(false); };
            if allocation.duplicate || allocation.after != instruction.offset {
                return Err(invalid(declaration));
            }
            stack.push(StackValue::Allocation(Allocation { duplicate: true, ..*allocation }));
        }
        (opcode @ (0xb6..=0xb8), Operand::Constant(index)) => {
            if !matches!(bytecode.class.pool.get(*index)?, Constant::Methodref { .. }) {
                return Ok(false);
            }
            let (owner, name, raw) = bytecode.class.pool.member_ref(*index)?;
            let call = if opcode == 0xb7 && name == "<init>" && !context.has_receiver() {
                let descriptor = MethodDescriptor::parse(raw)?;
                constructor(bytecode, context, locals, owner, descriptor, stack, declaration)?
            } else if owner == bytecode.owner && locals.instance && !context.has_receiver()
                && (opcode == 0xb6 || opcode == 0xb8 && name.ends_with("$default"))
            {
                let descriptor = MethodDescriptor::parse(raw)?;
                let Some(call) = member(bytecode, context, locals, name, descriptor, opcode == 0xb8, stack, declaration)? else {
                    return Ok(false);
                };
                call
            } else {
                return Ok(false);
            };
            if call.result.jvm == JvmType::Void {
                stack.push(StackValue::UnitCall(Box::new(call)));
            } else {
                let mut depth = call.arguments.iter().map(|arg| arg.value.depth).max().unwrap_or(0);
                if let Target::Member { receiver: Some(receiver), .. } = &call.target {
                    depth = depth.max(receiver.value.depth);
                }
                stack.push(StackValue::Value(Expr::new(ExprKind::Invocation(Box::new(call)), depth + 1, declaration)?));
            }
        }
        _ => return Ok(false),
    }
    Ok(true)
}

fn constructor<'a>(
    bytecode: &Bytecode<'a, '_>,
    context: &Context<'_>,
    locals: &Locals<'_>,
    owner: &'a str,
    descriptor: MethodDescriptor,
    stack: &mut Vec<StackValue<'a>>,
    declaration: &str,
) -> Result<Call<'a>, KotlinError> {
    let invalid = || invalid(declaration);
    let base = stack.len().checked_sub(descriptor.parameters.len() + 2).ok_or_else(invalid)?;
    if !matches!(&stack[base..base + 2], [StackValue::Allocation(first), StackValue::Allocation(second)]
        if first.owner == owner && second.owner == owner && first.after == second.after
            && !first.duplicate && second.duplicate)
    {
        return Err(invalid());
    }
    let class = if owner == bytecode.owner { bytecode.class } else {
        context.group.and_then(|group| group.get(owner)).ok_or_else(invalid)?
    };
    let metadata = context.owner(class, owner)?.ok_or_else(invalid)?;
    let [constructor] = metadata.constructors.as_slice() else { return Err(invalid()); };
    let caller_package = bytecode.owner.rsplit_once('/').map_or("", |(package, _)| package);
    let qualifier = metadata.name.id.split(['/', '.']).next().unwrap();
    let target = Bytecode { class, owner };
    if metadata.kind != ClassKind::Class
        || metadata.flags.has(9) || metadata.flags.has(13)
        || metadata.flags.visibility()? != Visibility::Public
        || metadata.name.package() != caller_package
        || caller_package.is_empty() && !bytecode.owner.split('$').next().is_some_and(|root| root == qualifier)
        || context.parameters.iter().any(|parameter| parameter.name == qualifier)
        || context.members.properties.iter().any(|property| property.name == qualifier)
        || !metadata.type_parameters.is_empty()
        || !metadata.context_receivers.is_empty() || constructor.flags.visibility()? != Visibility::Public
        || descriptor.return_type != JvmType::Void
        || !matches!(&constructor.signature, Some(signature)
            if signature.name == "<init>" && signature.descriptor == descriptor
                && public_instance(&target, signature)?)
        || !parameters_match(&constructor.parameters, &descriptor.parameters)
    {
        return Err(invalid());
    }
    let arguments = take_arguments(
        stack, base + 2, locals, &constructor.parameters, descriptor.parameters, &[], declaration,
    )?;
    stack.truncate(base);
    Ok(Call {
        target: Target::Constructor,
        arguments,
        result: Value {
            ty: class_type(metadata.name.clone()),
            jvm: JvmType::Object(owner.to_owned()),
        },
    })
}

fn member<'a>(
    bytecode: &Bytecode<'a, '_>,
    context: &Context<'_>,
    locals: &Locals<'_>,
    name: &str,
    invoked: MethodDescriptor,
    default: bool,
    stack: &mut Vec<StackValue<'a>>,
    declaration: &str,
) -> Result<Option<Call<'a>>, KotlinError> {
    let name = if default { name.strip_suffix("$default").unwrap() } else { name };
    let mut candidates = context.members.functions.iter().filter(|function| function.name == name);
    let Some(function) = candidates.next() else { return Ok(None); };
    let Some(signature) = &function.signature else { return Ok(None); };
    let invalid = || invalid(declaration);
    if signature.name != name || (!default && signature.descriptor != invoked) {
        return Ok(None);
    }
    if candidates.next().is_some() || context.members.properties.iter().any(|property| property.name == name)
        || function.flags.member_kind() != MemberKind::Declaration
        || function.flags.visibility()? != Visibility::Public || function.flags.has(10)
        || function.flags.has(13) || !function.type_parameters.is_empty()
        || !function.context_receivers.is_empty() || !function.context_parameters.is_empty()
        || !bare_superclass(bytecode.class)? || !public_instance(bytecode, signature)?
        || !exact_type(&function.returns, &signature.descriptor.return_type, false)
    {
        return Err(invalid());
    }
    let signature_parameters = &signature.descriptor.parameters;
    let (receiver, parameters) = if let Some(receiver) = &function.receiver {
        let Some((jvm, rest)) = signature_parameters.split_first() else { return Err(invalid()); };
        if default || receiver.nullable || !exact_type(receiver, jvm, false)
            || !unshadowed_extension(context, name, jvm)?
        {
            return Err(invalid());
        }
        (Some((receiver, jvm)), rest)
    } else {
        (None, signature_parameters.as_slice())
    };
    if !parameters_match(&function.parameters, parameters) {
        return Err(invalid());
    }
    let base = stack.len().checked_sub(invoked.parameters.len() + usize::from(!default)).ok_or_else(invalid)?;
    if !matches!(stack[base], StackValue::This) {
        return Err(invalid());
    }
    let omitted = if default {
        let omitted = omissions(
            bytecode, &invoked, &signature.descriptor, &function.parameters, stack, base + 1, declaration,
        )?;
        defaults::recover(bytecode, signature, &function.parameters, true, name)?;
        stack.truncate(base + 1 + parameters.len());
        omitted
    } else {
        Vec::new()
    };
    let args_start = 1 + usize::from(receiver.is_some());
    let arguments = take_arguments(
        stack, base + args_start, locals, &function.parameters,
        invoked.parameters.into_iter().skip(args_start - usize::from(!default)).take(parameters.len()),
        &omitted, declaration,
    )?;
    let receiver = if let Some((ty, jvm)) = receiver {
        let value = super::pop_value(stack, declaration)?;
        if !value.source_type(locals).is_some_and(|(source, actual)| source == ty && actual == jvm) {
            return Err(invalid());
        }
        Some(Argument { value, ty: ty.clone(), jvm: jvm.clone(), name: None })
    } else {
        None
    };
    stack.truncate(base);
    Ok(Some(Call {
        target: Target::Member { name: name.to_owned(), receiver },
        arguments,
        result: Value { ty: function.returns.clone(), jvm: invoked.return_type },
    }))
}

fn omissions(
    bytecode: &Bytecode<'_, '_>,
    invoked: &MethodDescriptor,
    target: &MethodDescriptor,
    parameters: &[ValueParameter],
    stack: &[StackValue<'_>],
    start: usize,
    declaration: &str,
) -> Result<Vec<bool>, KotlinError> {
    let invalid = || invalid(declaration);
    let masks = parameters.len().div_ceil(32);
    let count = parameters.len();
    let primitive = JvmType::Primitive(Primitive::Int);
    if invoked.parameters.len() != count + masks + 2 || invoked.return_type != target.return_type
        || !matches!(&invoked.parameters[0], JvmType::Object(owner) if owner == bytecode.owner)
        || invoked.parameters[1..count + 1] != target.parameters
        || invoked.parameters[count + 1..count + 1 + masks].iter().any(|mask| *mask != primitive)
        || !matches!(invoked.parameters.last(), Some(JvmType::Object(marker)) if marker == "java/lang/Object")
        || !matches!(stack.last(), Some(StackValue::Value(Expr { kind: ExprKind::Literal(Literal::Null), .. })))
        || !parameters.iter().any(|param| param.flags.has(1))
    {
        return Err(invalid());
    }
    let mut omitted = Vec::with_capacity(count);
    for (word, operand) in stack[start + count..start + count + masks].iter().enumerate() {
        let StackValue::Value(Expr { kind: ExprKind::Literal(Literal::Int(mask)), .. }) = operand else {
            return Err(invalid());
        };
        let word_start = word * 32;
        let width = (count - word_start).min(32);
        if width < 32 && (*mask as u32) >> width != 0 {
            return Err(invalid());
        }
        for bit in 0..width {
            let omit = (*mask as u32) & (1 << bit) != 0;
            if omit && !parameters[word_start + bit].flags.has(1) {
                return Err(invalid());
            }
            omitted.push(omit);
        }
    }
    if !omitted.contains(&true) {
        return Err(invalid());
    }
    Ok(omitted)
}

fn take_arguments<'a>(
    stack: &mut Vec<StackValue<'a>>,
    start: usize,
    locals: &Locals<'_>,
    parameters: &[ValueParameter],
    descriptor: impl IntoIterator<Item = JvmType>,
    omitted: &[bool],
    declaration: &str,
) -> Result<Vec<Argument<'a>>, KotlinError> {
    let mut arguments = Vec::with_capacity(parameters.len() - omitted.iter().filter(|&&omit| omit).count());
    let mut named = false;
    for (index, ((operand, parameter), jvm)) in stack.drain(start..).zip(parameters).zip(descriptor).enumerate() {
        let StackValue::Value(value) = operand else { return Err(invalid(declaration)); };
        if omitted.get(index) == Some(&true) {
            if !default_placeholder(&value, &jvm) {
                return Err(invalid(declaration));
            }
            named = true;
        } else if value.stack_load() != Some(load_opcode(&jvm))
            || value.source_type(locals).is_some_and(|(_, actual)| *actual != jvm)
        {
            return Err(invalid(declaration));
        } else {
            arguments.push(Argument { value, ty: parameter.ty.clone(), jvm, name: named.then(|| parameter.name.clone()) });
        }
    }
    Ok(arguments)
}

fn default_placeholder(value: &Expr<'_>, jvm: &JvmType) -> bool {
    match (&value.kind, load_opcode(jvm)) {
        (ExprKind::Literal(Literal::Null), 0x19)
        | (ExprKind::Literal(Literal::Int(0)), 0x15)
        | (ExprKind::Literal(Literal::Long(0)), 0x16) => true,
        (ExprKind::Literal(Literal::Float(value)), 0x17) => value.to_bits() == 0,
        (ExprKind::Literal(Literal::Double(value)), 0x18) => value.to_bits() == 0,
        _ => false,
    }
}

fn class_type(name: ClassName) -> Type {
    Type {
        classifier: Classifier::Class(name),
        arguments: Vec::new(),
        nullable: false,
        suspend: false,
        definitely_not_null: false,
        outer: None,
        abbreviated: None,
        flexible: None,
        raw: false,
        annotations: Vec::new(),
    }
}

fn parameters_match(parameters: &[ValueParameter], descriptor: &[JvmType]) -> bool {
    parameters.len() == descriptor.len() && parameters.iter().zip(descriptor).all(|(parameter, jvm)| {
        parameter.vararg_element.is_none() && exact_type(&parameter.ty, jvm, false)
    })
}

fn public_instance(bytecode: &Bytecode<'_, '_>, signature: &super::JvmMethodSignature) -> Result<bool, KotlinError> {
    Ok(bytecode.find_method(signature)?.is_some_and(|method| {
        method.access_flags & (0x0007 | STATIC | 0x0040 | 0x1000) == 0x0001
    }))
}

fn bare_superclass(class: &ClassFile<'_>) -> Result<bool, KotlinError> {
    Ok(class.interfaces.is_empty() && class.super_class != 0
        && class.pool.class_name(class.super_class)? == "java/lang/Object")
}

fn unshadowed_extension(context: &Context<'_>, name: &str, receiver: &JvmType) -> Result<bool, KotlinError> {
    let JvmType::Object(owner) = receiver else { return Ok(false); };
    let Some(class) = context.group.and_then(|group| group.get(owner)) else { return Ok(false); };
    let Some(metadata) = context.owner(class, owner)? else { return Ok(false); };
    if !bare_superclass(class)? || matches!(name, "equals" | "hashCode" | "toString" | "javaClass")
        || metadata.members.functions.iter().any(|function| function.name == name)
        || metadata.members.properties.iter().any(|property| property.name == name)
    {
        return Ok(false);
    }
    for method in &class.methods {
        if class.pool.utf8(method.name_index)? == name {
            return Ok(false);
        }
    }
    Ok(true)
}

fn invalid(declaration: &str) -> KotlinError {
    KotlinError::unsupported(declaration, "unproven Kotlin invocation")
}
