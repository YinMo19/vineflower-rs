// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.

//! Bind JVM calls to declarations before lowering their operands. A member
//! extension's dispatch receiver is lexical; its first argument is the source
//! receiver, not an ordinary argument.

use crate::{
    classfile::ClassFile,
    kotlin::{ClassKind, ClassName, Classifier, MemberKind, Visibility},
};

use super::{
    Bytecode, Constant, Expected, Expr, ExprKind, Function, Instruction, JvmType, KotlinError, Literal,
    Locals, MethodDescriptor, Operand, Primitive, STATIC, StackValue, Type, ValueParameter,
    defaults, extensions::{Context, Value, exact_type}, identifier, load_opcode, logic, qualified,
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
    Member { name: String },
    Extension { name: String, receiver: Argument<'a>, widen: bool, infix: bool },
    Function { name: String },
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
        self.write_at(out, parameters, declaration, 0)
    }

    pub(super) fn write_at(
        &self,
        out: &mut String,
        parameters: &[ValueParameter],
        declaration: &str,
        binding: u8,
    ) -> Result<(), KotlinError> {
        match &self.target {
            Target::Constructor => qualified(out, self.result.ty.class_id().unwrap(), declaration)?,
            Target::Member { name } => {
                out.push_str("this.");
                identifier(out, name, declaration)?;
            }
            Target::Extension { name, receiver, widen, infix } => {
                if *infix {
                    if binding > logic::INFIX {
                        out.push('(');
                    }
                    receiver.write_receiver(out, parameters, declaration, logic::INFIX, *widen)?;
                    out.push(' ');
                    identifier(out, name, declaration)?;
                    out.push(' ');
                    let [argument] = self.arguments.as_slice() else { return Err(invalid(declaration)); };
                    argument.value.write_at(
                        out, Expected::Type(&argument.ty, &argument.jvm), parameters, declaration, logic::INFIX + 1,
                    )?;
                    if binding > logic::INFIX {
                        out.push(')');
                    }
                    return Ok(());
                }
                receiver.write_receiver(out, parameters, declaration, u8::MAX, *widen)?;
                out.push('.');
                identifier(out, name, declaration)?;
            }
            Target::Function { name } => identifier(out, name, declaration)?,
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

impl Argument<'_> {
    fn write_receiver(
        &self, out: &mut String, parameters: &[ValueParameter], declaration: &str, binding: u8, widen: bool,
    ) -> Result<(), KotlinError> {
        let negative = binding == u8::MAX && matches!(self.value.kind, ExprKind::Literal(Literal::Int(n)) if n < 0);
        if widen || negative {
            out.push('(');
        }
        self.value.write_at(
            out, Expected::Type(&self.ty, &self.jvm), parameters, declaration,
            if widen { logic::INFIX + 1 } else { binding },
        )?;
        if widen {
            out.push_str(" as kotlin.CharSequence)");
        } else if negative {
            out.push(')');
        }
        Ok(())
    }
}

const REPEAT: (&str, &str, &str) = ("kotlin/text/StringsKt", "repeat", "(Ljava/lang/CharSequence;I)Ljava/lang/String;");

pub(in crate::kotlin) fn uses_stdlib_repeat(class: &ClassFile<'_>) -> Result<bool, KotlinError> {
    let pool = &class.pool;
    for entry in pool.iter() {
        if let Constant::Methodref { class_index, name_and_type_index } = entry
            && pool.class_name(*class_index)? == REPEAT.0
            && pool.name_and_type(*name_and_type_index)? == (REPEAT.1, REPEAT.2)
        {
            return Ok(true);
        }
    }
    Ok(false)
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
        (0xc0, Operand::Constant(index))
            if bytecode.class.pool.class_name(*index)? == "java/lang/CharSequence"
                && matches!(stack.last(), Some(StackValue::Value(value))
                    if is_char_sequence_operand(value, locals)) =>
        {
            // This checkcast is an upcast from a proven Kotlin String or
            // CharSequence. Leave the precise source type on the stack.
        }
        (opcode @ (0xb6..=0xb8), Operand::Constant(index)) => {
            if !matches!(bytecode.class.pool.get(*index)?, Constant::Methodref { .. }) {
                return Ok(false);
            }
            let (owner, name, raw) = bytecode.class.pool.member_ref(*index)?;
            let call = if opcode == 0xb7 && name == "<init>" && !context.has_receiver() {
                let descriptor = MethodDescriptor::parse(raw)?;
                constructor(bytecode, context, locals, owner, descriptor, stack, declaration)?
            } else if opcode == 0xb8 && (owner, name, raw) == REPEAT {
                stdlib_repeat(bytecode, context, locals, stack, declaration)?
            } else if opcode == 0xb8 && owner == bytecode.owner
                && let Some(local) = context.local_functions.iter().find(|local|
                    local.descriptor == raw && local.function.signature.as_ref().unwrap().name == name)
            {
                local_extension(context, locals, &local.function, stack, declaration)?
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
                stack.push(StackValue::Value(call_expression(Box::new(call), declaration)?));
            }
        }
        _ => return Ok(false),
    }
    Ok(true)
}

fn call_expression<'a>(call: Box<Call<'a>>, declaration: &str) -> Result<Expr<'a>, KotlinError> {
    let mut depth = call.arguments.iter().map(|arg| arg.value.depth).max().unwrap_or(0);
    if let Target::Extension { receiver, .. } = &call.target {
        depth = depth.max(receiver.value.depth);
    }
    Expr::new(ExprKind::Invocation(call), depth + 1, declaration)
}

pub(super) fn tail_call<'a>(
    bytecode: &Bytecode<'a, '_>,
    locals: &Locals<'_>,
    stack: &mut Vec<StackValue<'a>>,
    declaration: &str,
) -> Result<Expr<'a>, KotlinError> {
    let invalid = || invalid(declaration);
    let context = locals.extension.as_ref().ok_or_else(invalid)?;
    let function = context.function;
    let signature = function.signature.as_ref().ok_or_else(invalid)?;
    let descriptor = &signature.descriptor;
    if function.name != signature.name || function.receiver.is_some()
        || !function.type_parameters.is_empty()
        || stack.len() != function.parameters.len()
        || !parameters_match(&function.parameters, &descriptor.parameters)
        || !exact_type(&function.returns, &descriptor.return_type, false)
        || !bare_superclass(bytecode.class)?
        || !unambiguous(context, function, false)
        || (!locals.instance && context.parameters.iter().any(|parameter| parameter.name == function.name))
    {
        return Err(invalid());
    }
    let arguments = take_arguments(
        stack, 0, locals, &function.parameters, descriptor.parameters.iter().cloned(), &[], declaration,
    )?;
    let name = function.name.clone();
    let target = if locals.instance { Target::Member { name } } else { Target::Function { name } };
    call_expression(Box::new(Call {
        target,
        arguments,
        result: Value { ty: function.returns.clone(), jvm: descriptor.return_type.clone() },
    }), declaration)
}

#[derive(Clone, Copy, Debug)]
pub(super) enum GuardedMember {
    PrintStackTrace,
}

impl GuardedMember {
    pub(super) fn write(self, out: &mut String) {
        match self {
            Self::PrintStackTrace => out.push_str("?.printStackTrace()"),
        }
    }
}

pub(super) fn throwable_owner(ty: &Type, jvm: &JvmType) -> Option<&'static str> {
    match (jvm, ty.class_id()) {
        (JvmType::Object(owner), Some("kotlin/Exception" | "java/lang/Exception"))
            if owner == "java/lang/Exception" => Some("java/lang/Exception"),
        (JvmType::Object(owner), Some("kotlin/Throwable" | "java/lang/Throwable"))
            if owner == "java/lang/Throwable" => Some("java/lang/Throwable"),
        _ => None,
    }
}

/// External calls without metadata require an exact, known Java signature.
/// The nullable region has already proved that this call gets the retained
/// receiver and no other operands.
pub(super) fn guarded_member(
    bytecode: &Bytecode<'_, '_>,
    instruction: &Instruction,
    ty: &Type,
    jvm: &JvmType,
    declaration: &str,
) -> Result<GuardedMember, KotlinError> {
    let owner = throwable_owner(ty, jvm).ok_or_else(|| invalid(declaration))?;
    if !matches!(instruction.operand, Operand::Constant(index)
        if matches!(bytecode.class.pool.get(index)?, Constant::Methodref { .. }))
        || !matches!(bytecode.reference(instruction, 0xb6)?,
            Some((target, "printStackTrace", "()V"))
                if target == owner || target == "java/lang/Throwable")
    {
        return Err(invalid(declaration));
    }
    Ok(GuardedMember::PrintStackTrace)
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
    if owner == "java/lang/Exception" && descriptor.return_type == JvmType::Void
        && descriptor.parameters.is_empty()
    {
        if context.parameters.iter().any(|parameter| parameter.name == "kotlin")
            || context.members.properties.iter().any(|property| property.name == "kotlin")
        {
            return Err(invalid());
        }
        stack.truncate(base);
        return Ok(Call {
            target: Target::Constructor,
            arguments: Vec::new(),
            result: Value {
                ty: class_type(ClassName { id: "kotlin/Exception".into(), local: false }),
                jvm: JvmType::Object(owner.into()),
            },
        });
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

fn is_string_expression(value: &Expr<'_>) -> bool {
    matches!(value.kind, ExprKind::Literal(Literal::String(_)) | ExprKind::Template(_))
}

fn is_char_sequence_type(ty: &Type, jvm: &JvmType) -> bool {
    !ty.nullable && matches!(ty.class_id(), Some("kotlin/String" | "kotlin/CharSequence"))
        && exact_type(ty, jvm, false)
}

fn is_char_sequence_operand(value: &Expr<'_>, locals: &Locals<'_>) -> bool {
    is_string_expression(value) || value.source_type(locals).is_some_and(|(ty, jvm)| is_char_sequence_type(ty, jvm))
}

fn char_sequence_receiver<'a>(
    value: Expr<'a>, locals: &Locals<'_>, declaration: &str,
) -> Result<(Argument<'a>, bool), KotlinError> {
    let (ty, jvm) = match value.source_type(locals) {
        Some((ty, jvm)) if is_char_sequence_type(ty, jvm) => (ty.clone(), jvm.clone()),
        None if is_string_expression(&value) => {
            (kotlin_type("kotlin/String"), JvmType::Object("java/lang/String".into()))
        }
        _ => return Err(invalid(declaration)),
    };
    let widen = ty.class_id() == Some("kotlin/String");
    Ok((Argument { value, ty, jvm, name: None }, widen))
}

fn receiver_argument<'a>(
    value: Expr<'a>, ty: &Type, jvm: &JvmType, locals: &Locals<'_>, declaration: &str,
) -> Result<(Argument<'a>, bool), KotlinError> {
    if value.source_type(locals).is_some_and(|(source, actual)| source == ty && actual == jvm)
        || matches!(jvm, JvmType::Primitive(primitive) if
            (matches!(value.kind, ExprKind::Literal(Literal::Int(_))) && *primitive == Primitive::Int)
                || locals.extension.as_ref().is_some_and(|context|
                    value.primitive_hint(context.parameters) == Some(*primitive)))
    {
        Ok((Argument { value, ty: ty.clone(), jvm: jvm.clone(), name: None }, false))
    } else if ty.class_id() == Some("kotlin/CharSequence") {
        char_sequence_receiver(value, locals, declaration)
    } else {
        Err(invalid(declaration))
    }
}

fn stdlib_repeat<'a>(
    bytecode: &Bytecode<'a, '_>,
    context: &Context<'_>,
    locals: &Locals<'_>,
    stack: &mut Vec<StackValue<'a>>,
    declaration: &str,
) -> Result<Call<'a>, KotlinError> {
    // kotlin.text declares `fun CharSequence.repeat(n: Int): String`;
    // StringsKt's inherited static method is the JVM facade for that API.
    let name = REPEAT.1;
    if !bare_superclass(bytecode.class)?
        || context.function.name == name
        || context.members.functions.iter().any(|function| function.name == name)
        || context.members.properties.iter().any(|property| property.name == name)
        || context.local_functions.iter().any(|local| local.function.name == name)
        || context.parameters.iter().any(|parameter| parameter.name == name)
    {
        return Err(invalid(declaration));
    }
    let value = super::pop_value(stack, declaration)?;
    let jvm = JvmType::Primitive(Primitive::Int);
    if value.stack_load() != Some(0x15)
        || !(matches!(value.kind, ExprKind::Literal(Literal::Int(_)))
            || value.primitive_hint(context.parameters) == Some(Primitive::Int))
    {
        return Err(invalid(declaration));
    }
    let argument = Argument { value, ty: kotlin_type("kotlin/Int"), jvm, name: None };
    let (receiver, _) = char_sequence_receiver(super::pop_value(stack, declaration)?, locals, declaration)?;
    Ok(Call {
        target: Target::Extension { name: name.into(), receiver, widen: false, infix: false },
        arguments: vec![argument],
        result: Value { ty: kotlin_type("kotlin/String"), jvm: JvmType::Object("java/lang/String".into()) },
    })
}

fn local_extension<'a>(
    context: &Context<'_>,
    locals: &Locals<'_>,
    function: &Function,
    stack: &mut Vec<StackValue<'a>>,
    declaration: &str,
) -> Result<Call<'a>, KotlinError> {
    let descriptor = &function.signature.as_ref().unwrap().descriptor;
    let base = stack.len().checked_sub(descriptor.parameters.len()).ok_or_else(|| invalid(declaration))?;
    let (receiver, parameters) = descriptor.parameters.split_first().unwrap();
    if !unshadowed_extension(context, function, receiver, parameters)? {
        return Err(invalid(declaration));
    }
    let arguments = take_arguments(
        stack, base + 1, locals, &function.parameters, parameters.iter().cloned(), &[], declaration,
    )?;
    let (receiver, widen) = receiver_argument(
        super::pop_value(stack, declaration)?, function.receiver.as_ref().unwrap(), receiver, locals, declaration,
    )?;
    Ok(Call {
        target: Target::Extension { name: function.name.clone(), receiver, widen, infix: true },
        arguments,
        result: Value { ty: function.returns.clone(), jvm: descriptor.return_type.clone() },
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
    let Some(function) = context.members.functions.iter().find(|function| {
        function.name == name && function.signature.as_ref().is_some_and(|signature| {
            signature.name == name && (default || signature.descriptor == invoked)
        })
    }) else { return Ok(None); };
    let Some(signature) = &function.signature else { return Ok(None); };
    let invalid = || invalid(declaration);
    if !unambiguous(context, function, default)
        || context.local_functions.iter().any(|local| local.function.name == name)
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
            || context.parameters.iter().any(|parameter| parameter.name == name)
            || !unshadowed_extension(context, function, jvm, rest)?
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
    let name = name.to_owned();
    let target = if let Some((ty, jvm)) = receiver {
        let (receiver, widen) = receiver_argument(
            super::pop_value(stack, declaration)?, ty, jvm, locals, declaration,
        )?;
        Target::Extension { name, receiver, widen, infix: function.flags.has(9) && arguments.len() == 1 }
    } else {
        Target::Member { name }
    };
    stack.truncate(base);
    Ok(Some(Call {
        target,
        arguments,
        result: Value { ty: function.returns.clone(), jvm: invoked.return_type },
    }))
}

fn unambiguous(context: &Context<'_>, function: &Function, default: bool) -> bool {
    if context.members.properties.iter().any(|property| property.name == function.name) {
        return false;
    }
    let arity = function.parameters.len();
    context.members.functions.iter().all(|other| {
        if std::ptr::eq(function, other) || function.name != other.name {
            return true;
        }
        if default || function.receiver.is_some() || other.receiver.is_some()
            || other.parameters.iter().any(|parameter| parameter.vararg_element.is_some())
        {
            return false;
        }
        if other.parameters.len() < arity {
            return true;
        }
        let (prefix, rest) = other.parameters.split_at(arity);
        // A longer overload with the same supplied types can only compete
        // through defaults. Kotlin prefers the candidate omitting none.
        !rest.is_empty() && (rest.iter().any(|parameter| !parameter.flags.has(1))
            || (other.type_parameters.is_empty()
                && other.context_receivers.is_empty() && other.context_parameters.is_empty()
                && prefix.iter().zip(&function.parameters).all(|(a, b)| a.ty == b.ty)))
    })
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

pub(super) fn kotlin_type(id: &str) -> Type {
    class_type(ClassName { id: id.to_owned(), local: false })
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

fn unshadowed_extension(
    context: &Context<'_>, function: &Function, receiver: &JvmType, parameters: &[JvmType],
) -> Result<bool, KotlinError> {
    let name = function.name.as_str();
    if matches!(name, "equals" | "hashCode" | "toString" | "javaClass") {
        return Ok(false);
    }
    if let JvmType::Primitive(Primitive::Int) = receiver {
        return Ok(match name {
            // The built-in Int.times overloads take numeric operands only.
            "times" => matches!(parameters, [JvmType::Object(owner)] if owner == "java/lang/String"),
            "compareTo" | "plus" | "minus" | "div" | "rem" | "rangeTo" | "rangeUntil"
            | "unaryPlus" | "unaryMinus" | "inc" | "dec" | "shl" | "shr" | "ushr"
            | "and" | "or" | "xor" | "inv" | "toByte" | "toChar" | "toDouble" | "toFloat"
            | "toInt" | "toLong" | "toShort" | "byteValue" | "doubleValue" | "floatValue"
            | "intValue" | "longValue" | "shortValue" | "mod" => false,
            _ => true,
        });
    }
    let JvmType::Object(owner) = receiver else { return Ok(false); };
    if owner == "java/lang/CharSequence" {
        return Ok(!matches!(name, "get" | "length" | "charAt" | "subSequence" | "chars" | "codePoints" | "isEmpty"));
    }
    let Some(class) = context.group.and_then(|group| group.get(owner)) else { return Ok(false); };
    let Some(metadata) = context.owner(class, owner)? else { return Ok(false); };
    if !bare_superclass(class)?
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
