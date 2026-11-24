// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.

//! Bind JVM calls to declarations before lowering their operands. A member
//! extension's dispatch receiver is lexical; its first argument is the source
//! receiver, not an ordinary argument.

use crate::{
    classfile::ClassFile,
    kotlin::{ClassKind, ClassName, Classifier, MemberKind, TypeArgument, Variance, Visibility},
};

use super::{
    Bytecode, Constant, Expected, Expr, ExprKind, Function, Instruction, JvmType, KotlinError, Literal,
    Locals, MethodDescriptor, Operand, Primitive, STATIC, StackValue, Type, ValueParameter,
    defaults, extensions::{Context, Value, exact_type}, identifier, load_opcode, local_load, logic, qualified,
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
    RefConstructor,
    Member { name: String },
    Extension { name: String, receiver: Argument<'a>, widen: bool, infix: bool },
    Function { name: String },
    FunctionValue { receiver: Argument<'a>, erasure: IntErasure },
}

#[derive(Debug)]
enum IntErasure {
    Object { next: u32 },
    Number { next: u32 },
    Unboxed,
}

#[derive(Debug)]
struct Argument<'a> {
    value: ArgumentValue<'a>,
    ty: Type,
    jvm: JvmType,
    name: Option<String>,
}

#[derive(Debug)]
enum ArgumentValue<'a> {
    Single(Expr<'a>),
    Vararg(Vararg<'a>),
}

#[derive(Debug)]
pub(super) enum Vararg<'a> {
    Packed(Vec<Expr<'a>>),
    Spread { array: Expr<'a>, nullable_element: bool },
}

impl Call<'_> {
    pub(super) fn named_suspend(name: &str, ty: &Type, jvm: &JvmType) -> Self {
        Self {
            target: Target::Function { name: name.to_owned() },
            arguments: Vec::new(),
            result: Value { ty: ty.clone(), jvm: jvm.clone() },
        }
    }

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
            Target::RefConstructor => {
                qualified(out, self.result.ty.class_id().unwrap(), declaration)?;
                if !self.result.ty.arguments.is_empty() {
                    out.push_str("<kotlin.Any?>");
                }
            }
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
                    let [Argument { value: ArgumentValue::Single(value), ty, jvm, .. }] = self.arguments.as_slice()
                        else { return Err(invalid(declaration)); };
                    value.write_at(
                        out, Expected::Type(ty, jvm), parameters, declaration, logic::INFIX + 1,
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
            Target::FunctionValue { receiver, erasure: IntErasure::Unboxed } => {
                // Parenthesize nonlocal receivers so a call with the same
                // name as a function-valued property cannot win resolution.
                let grouped = !matches!(&receiver.value, ArgumentValue::Single(Expr {
                    kind: ExprKind::Parameter { .. } | ExprKind::Local(_) | ExprKind::Capture(_), ..
                }));
                if grouped { out.push('('); }
                receiver.write_receiver(out, parameters, declaration, if grouped { 0 } else { u8::MAX }, false)?;
                if grouped { out.push(')'); }
            }
            Target::FunctionValue { .. } => return Err(invalid(declaration)),
        }
        out.push('(');
        let mut separated = false;
        for argument in &self.arguments {
            let mut write = |value: &Expr<'_>, spread| {
                if separated {
                    out.push_str(", ");
                }
                separated = true;
                if let Some(name) = &argument.name {
                    identifier(out, name, declaration)?;
                    out.push_str(" = ");
                }
                if spread {
                    out.push('*');
                    value.write_at(out, Expected::Reference, parameters, declaration, 0)
                } else {
                    value.write(out, &argument.ty, &argument.jvm, parameters, declaration)
                }
            };
            match &argument.value {
                ArgumentValue::Single(value) => write(value, false)?,
                ArgumentValue::Vararg(Vararg::Spread { array, .. }) => write(array, true)?,
                ArgumentValue::Vararg(Vararg::Packed(elements)) => {
                    for value in elements {
                        write(value, false)?;
                    }
                }
            }
        }
        out.push(')');
        Ok(())
    }
}

impl<'a> Argument<'a> {
    fn single(value: Expr<'a>, ty: Type, jvm: JvmType, name: Option<String>) -> Self {
        Argument { value: ArgumentValue::Single(value), ty, jvm, name }
    }

    fn depth(&self) -> u8 {
        match &self.value {
            ArgumentValue::Single(value) | ArgumentValue::Vararg(Vararg::Spread { array: value, .. }) => value.depth,
            ArgumentValue::Vararg(Vararg::Packed(elements)) => elements.iter().map(|value| value.depth).max().unwrap_or(0),
        }
    }

    fn write_receiver(
        &self, out: &mut String, parameters: &[ValueParameter], declaration: &str, binding: u8, widen: bool,
    ) -> Result<(), KotlinError> {
        let ArgumentValue::Single(value) = &self.value else { return Err(invalid(declaration)); };
        let negative = binding == u8::MAX && matches!(value.kind, ExprKind::Literal(Literal::Int(n)) if n < 0);
        if widen || negative {
            out.push('(');
        }
        value.write_at(
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
const IS_BLANK: (&str, &str, &str) = ("kotlin/text/StringsKt", "isBlank", "(Ljava/lang/CharSequence;)Z");
const DROP: (&str, &str, &str) = ("kotlin/text/StringsKt", "drop", "(Ljava/lang/String;I)Ljava/lang/String;");
const IS_BLANK_ALIAS: &str = "lambdaTextIsBlank";
const DROP_ALIAS: &str = "lambdaTextDrop";

pub(in crate::kotlin) const TEXT_IMPORTS: [&str; 3] = [
    "kotlin.text.repeat",
    "kotlin.text.isBlank as lambdaTextIsBlank",
    "kotlin.text.drop as lambdaTextDrop",
];
const COPY_OF: (&str, &str, &str) = ("java/util/Arrays", "copyOf", "([Ljava/lang/Object;I)[Ljava/lang/Object;");
const STRING: &str = "java/lang/String";
const FUNCTION0: &str = "kotlin/jvm/functions/Function0";
const NUMBER: &str = "java/lang/Number";

pub(super) fn string_array_element<'a>(ty: &'a Type, jvm: &JvmType) -> Option<&'a Type> {
    let [TypeArgument::Type(Variance::Invariant | Variance::Out, element)] = ty.arguments.as_slice()
        else { return None; };
    let JvmType::Array(component) = jvm else { return None; };
    (ty.class_id() == Some("kotlin/Array") && !ty.nullable
        && element.class_id() == Some("kotlin/String")
        && matches!(component.as_ref(), JvmType::Object(owner) if owner == STRING)
        && exact_type(ty, jvm, false)).then_some(element)
}

pub(super) fn spread<'a>(
    bytecode: &Bytecode<'a, '_>, instructions: &[Instruction], locals: &Locals<'_>,
) -> Result<Option<Vararg<'a>>, KotlinError> {
    let [load, reload, length, copy, cast, ..] = instructions else { return Ok(None); };
    let Some((0x19, slot)) = local_load(load) else { return Ok(None); };
    if local_load(reload) != Some((0x19, slot)) || length.opcode != 0xbe
        || copy.opcode != 0xb8 || cast.opcode != 0xc0
    {
        return Ok(None);
    }
    let (Operand::Constant(method), Operand::Constant(class)) = (&copy.operand, &cast.operand)
        else { return Ok(None); };
    let pool = &bytecode.class.pool;
    if !matches!(pool.get(*method)?, Constant::Methodref { .. }) || pool.member_ref(*method)? != COPY_OF
        || pool.class_name(*class)? != "[Ljava/lang/String;"
    {
        return Ok(None);
    }
    let Some(index) = locals.parameter(slot, 0x19) else { return Ok(None); };
    let Some(context) = &locals.extension else { return Ok(None); };
    let Some(element) = string_array_element(&context.parameters[index].ty, locals.slots[index].1)
        else { return Ok(None); };
    // A spread of a parameter creates the same full-length copy, including
    // the runtime component type. A direct load is not a spread.
    Ok(Some(Vararg::Spread {
        array: Expr { kind: ExprKind::Parameter { index, load: 0x19 }, depth: 1 },
        nullable_element: element.nullable,
    }))
}

/// Recognize the writes to a private, freshly allocated compiler pack.
/// Kotlin/JVM uses either a scratch local or `dup` to keep the array live.
pub(super) fn packed<'a>(
    bytecode: &Bytecode<'a, '_>,
    instructions: &[Instruction],
    length: i32,
    mut lower: impl FnMut(&Instruction, &mut Vec<StackValue<'a>>) -> Result<(), KotlinError>,
    declaration: &str,
) -> Result<(Vararg<'a>, usize, Option<u16>), KotlinError> {
    let invalid = || invalid(declaration);
    let [allocate, tail @ ..] = instructions else { return Err(invalid()); };
    let Operand::Constant(class) = allocate.operand else { return Err(invalid()); };
    let length = usize::try_from(length).map_err(|_| invalid())?;
    if allocate.opcode != 0xbd || bytecode.class.pool.class_name(class)? != STRING || length > tail.len() / 4 {
        return Err(invalid());
    }
    let scratch = tail.first().and_then(super::local_store).and_then(|(op, slot)| (op == 0x3a).then_some(slot));
    let mut index = 1 + usize::from(scratch.is_some());
    let reload = |instruction: &Instruction| {
        scratch.is_some_and(|slot| local_load(instruction) == Some((0x19, slot)))
    };
    let mut elements = Vec::with_capacity(length);
    let mut value_stack = Vec::new();
    for ordinal in 0..length {
        let Some([array, key, ..]) = instructions.get(index..) else { return Err(invalid()); };
        if !(if scratch.is_some() { reload(array) } else { array.opcode == 0x59 })
            || !matches!(key.opcode, 0x02..=0x08 | 0x10..=0x13)
        {
            return Err(invalid());
        }
        lower(key, &mut value_stack)?;
        if !matches!(value_stack.pop(), Some(StackValue::Value(Expr { kind: ExprKind::Literal(Literal::Int(key)), .. }))
            if usize::try_from(key) == Ok(ordinal))
        {
            return Err(invalid());
        }
        index += 2;
        while let Some(instruction) = instructions.get(index).filter(|instruction| instruction.opcode != 0x53) {
            if scratch.is_some_and(|slot| instruction.local_access().is_some_and(|(range, _)| range.contains(&u32::from(slot)))) {
                return Err(invalid());
            }
            lower(instruction, &mut value_stack)?;
            index += 1;
        }
        if index == instructions.len() || value_stack.len() != 1 {
            return Err(invalid());
        }
        elements.push(super::pop_value(&mut value_stack, declaration)?);
        index += 1;
    }
    if scratch.is_some() {
        if !instructions.get(index).is_some_and(reload) {
            return Err(invalid());
        }
        index += 1;
    }
    Ok((Vararg::Packed(elements), index, scratch))
}

pub(in crate::kotlin) fn text_imports(class: &ClassFile<'_>) -> Result<u8, KotlinError> {
    let pool = &class.pool;
    let mut mask = 0;
    for entry in pool.iter() {
        if let Constant::Methodref { class_index, name_and_type_index } = entry
            && pool.class_name(*class_index)? == REPEAT.0
        {
            mask |= match pool.name_and_type(*name_and_type_index)? {
                (name, descriptor) if (name, descriptor) == (REPEAT.1, REPEAT.2) => 1,
                (name, descriptor) if (name, descriptor) == (IS_BLANK.1, IS_BLANK.2) => 2,
                (name, descriptor) if (name, descriptor) == (DROP.1, DROP.2) => 4,
                _ => 0,
            };
        }
    }
    Ok(mask)
}

pub(super) fn lambda_text<'a>(
    bytecode: &Bytecode<'a, '_>, instruction: &Instruction, locals: &Locals<'_>,
    stack: &mut Vec<StackValue<'a>>, declaration: &str,
) -> Result<bool, KotlinError> {
    let (name, source, result, arguments) = match bytecode.reference(instruction, 0xb8)? {
        Some(IS_BLANK) => (
            IS_BLANK_ALIAS, "kotlin/CharSequence",
            Value { ty: kotlin_type("kotlin/Boolean"), jvm: JvmType::Primitive(Primitive::Boolean) }, Vec::new(),
        ),
        Some(DROP) => {
            let count = super::pop_value(stack, declaration)?;
            if count.primitive_hint(&[]) != Some(Primitive::Int)
                && !matches!(count.kind, ExprKind::Literal(Literal::Int(_)))
            {
                return Err(invalid(declaration));
            }
            (
                DROP_ALIAS, "kotlin/String",
                Value { ty: kotlin_type("kotlin/String"), jvm: JvmType::Object(STRING.into()) },
                vec![Argument::single(count, kotlin_type("kotlin/Int"), JvmType::Primitive(Primitive::Int), None)],
            )
        }
        _ => return Ok(false),
    };
    let receiver = super::pop_value(stack, declaration)?;
    let (ty, jvm) = receiver.source_type(locals).filter(|(ty, jvm)| {
        ty.simple_class(source) && !ty.nullable && exact_type(ty, jvm, false)
    }).ok_or_else(|| invalid(declaration))?;
    let (ty, jvm) = (ty.clone(), jvm.clone());
    let call = Box::new(Call {
        target: Target::Extension { name: name.into(), receiver: Argument::single(receiver, ty, jvm, None), widen: false, infix: false },
        arguments, result,
    });
    stack.push(StackValue::Value(call_expression(call, declaration)?));
    Ok(true)
}

/// A non-null Kotlin `() -> Int` is called through Function0's erased
/// descriptor. Only the exact Number cast and virtual unboxing complete
/// the source-level call; an erased intermediate is never printable.
pub(super) fn function_value<'a>(
    bytecode: &Bytecode<'a, '_>, instruction: &Instruction, locals: &Locals<'_>,
    stack: &mut Vec<StackValue<'a>>, declaration: &str,
) -> Result<bool, KotlinError> {
    let pool = &bytecode.class.pool;
    let after = instruction.offset + instruction.len;
    if let Some(StackValue::Value(Expr { kind: ExprKind::Invocation(call), .. })) = stack.last_mut()
        && let Target::FunctionValue { erasure, .. } = &mut call.target
    {
        match *erasure {
            IntErasure::Object { next } => {
                if next != instruction.offset || instruction.opcode != 0xc0
                    || !matches!(instruction.operand, Operand::Constant(index) if pool.class_name(index)? == NUMBER)
                {
                    return Err(invalid(declaration));
                }
                call.result.jvm = JvmType::Object(NUMBER.into());
                *erasure = IntErasure::Number { next: after };
                return Ok(true);
            }
            IntErasure::Number { next } => {
                if next != instruction.offset
                    || !matches!(instruction.operand, Operand::Constant(index) if matches!(pool.get(index)?, Constant::Methodref { .. }))
                    || bytecode.reference(instruction, 0xb6)? != Some((NUMBER, "intValue", "()I"))
                {
                    return Err(invalid(declaration));
                }
                call.result.jvm = JvmType::Primitive(Primitive::Int);
                *erasure = IntErasure::Unboxed;
                return Ok(true);
            }
            IntErasure::Unboxed => {}
        }
    }

    let (0xb9, Operand::InvokeInterface { index, count: 1 }) = (instruction.opcode, &instruction.operand)
        else { return Ok(false); };
    if !matches!(pool.get(*index)?, Constant::InterfaceMethodref { .. })
        || pool.member_ref(*index)? != (FUNCTION0, "invoke", "()Ljava/lang/Object;")
    {
        return Ok(false);
    }
    let Some(StackValue::Value(receiver)) = stack.last() else { return Ok(false); };
    let Some((ty, jvm @ JvmType::Object(owner))) = receiver.source_type(locals) else { return Ok(false); };
    if owner != FUNCTION0 || !ty.simple_class("kotlin/Function0") || ty.nullable {
        return Ok(false);
    }
    let [TypeArgument::Type(Variance::Invariant | Variance::Out, result)] = ty.arguments.as_slice()
        else { return Ok(false); };
    if !result.simple_class("kotlin/Int") || result.nullable || !result.arguments.is_empty() {
        return Ok(false);
    }
    let (ty, jvm, result) = (ty.clone(), jvm.clone(), result.clone());
    let receiver = super::pop_value(stack, declaration)?;
    let call = Box::new(Call {
        target: Target::FunctionValue {
            receiver: Argument::single(receiver, ty, jvm, None),
            erasure: IntErasure::Object { next: after },
        },
        arguments: Vec::new(),
        result: Value { ty: result, jvm: JvmType::Object("java/lang/Object".into()) },
    });
    stack.push(StackValue::Value(call_expression(call, declaration)?));
    Ok(true)
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
    let mut depth = call.arguments.iter().map(Argument::depth).max().unwrap_or(0);
    if let Target::Extension { receiver, .. } | Target::FunctionValue { receiver, .. } = &call.target {
        depth = depth.max(receiver.depth());
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
    if locals.closure_body && descriptor.return_type == JvmType::Void && descriptor.parameters.is_empty()
        && let Some(ty) = super::lambdas::ref_type(owner)
        && !super::lambdas::namespace_shadowed(locals)
    {
        stack.truncate(base);
        return Ok(Call {
            target: Target::RefConstructor,
            arguments: Vec::new(),
            result: Value { ty, jvm: JvmType::Object(owner.into()) },
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
    Ok((Argument::single(value, ty, jvm, None), widen))
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
        Ok((Argument::single(value, ty.clone(), jvm.clone(), None), false))
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
    let argument = Argument::single(value, kotlin_type("kotlin/Int"), jvm, None);
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
    if !member_parameters_match(&function.parameters, parameters, !default && receiver.is_none()) {
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
        if function.parameters.iter().any(|parameter| parameter.vararg_element.is_some()) {
            return false;
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
        if let Some(ty) = &parameter.vararg_element {
            let StackValue::Vararg(value) = operand else { return Err(invalid(declaration)); };
            let JvmType::Array(component) = jvm else { return Err(invalid(declaration)); };
            // Dropping a copy or spreading a freshly built array would change
            // which array reaches the callee. Emit elements only for a proven pack.
            let jvm = *component;
            let valid = match &value {
                Vararg::Packed(elements) => elements.iter().all(|value| {
                    if let Some((source, actual)) = value.source_type(locals) {
                        *actual == jvm && Expected::Type(ty, &jvm).accepts(source)
                    } else {
                        is_string_expression(value)
                            || ty.nullable && matches!(value.kind, ExprKind::Literal(Literal::Null))
                    }
                }),
                Vararg::Spread { nullable_element, .. } => !*nullable_element || ty.nullable,
            };
            if !valid || named || omitted.get(index) == Some(&true) {
                return Err(invalid(declaration));
            }
            arguments.push(Argument { value: ArgumentValue::Vararg(value), ty: ty.clone(), jvm, name: None });
        } else {
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
                arguments.push(Argument::single(value, parameter.ty.clone(), jvm, named.then(|| parameter.name.clone())));
            }
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

fn member_parameters_match(parameters: &[ValueParameter], descriptor: &[JvmType], allow_vararg: bool) -> bool {
    if let ([fixed @ .., vararg], [jvm_fixed @ .., jvm_vararg]) = (parameters, descriptor)
        && let Some(element) = &vararg.vararg_element
    {
        return allow_vararg && parameters_match(fixed, jvm_fixed)
            && string_array_element(&vararg.ty, jvm_vararg) == Some(element);
    }
    parameters_match(parameters, descriptor)
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
