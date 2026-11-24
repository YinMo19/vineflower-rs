// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.

//! Reconstruct metafactory closures from their implementation handle. A
//! captured value is a binding at the call site, never the helper's slot name.

use std::rc::Rc;

use crate::kotlin::{Modality, TypeArgument, Variance};

use super::{
    Bytecode, Constant, Expected, Expr, ExprKind, FINAL, Instruction, JvmType, KotlinError, Locals,
    MethodDescriptor, Operand, Primitive, STATIC, StackValue, Type, ValueParameter,
    extensions::{Value, exact_type}, identifier, invocations::kotlin_type, load_opcode,
    local_functions::builtin_type, logic, loops::Element, pop_value, qualified,
    statements::{self, Statement},
};

const FUNCTION0: &str = "kotlin/jvm/functions/Function0";
const INT_REF: &str = "kotlin/jvm/internal/Ref$IntRef";
const OBJECT_REF: &str = "kotlin/jvm/internal/Ref$ObjectRef";
const OBJECT: &str = "java/lang/Object";

#[derive(Debug)]
pub(super) struct Closure<'a> {
    pub(super) value: Value,
    checks: Vec<(Rc<Capture>, &'a str, &'a str)>,
    body: ClosureBody<'a>,
}

#[derive(Debug)]
enum ClosureBody<'a> {
    Straight(Vec<Statement<'a>>),
    While { condition: Expr<'a>, statements: Vec<Statement<'a>> },
}

#[derive(Debug)]
pub(super) struct Capture {
    source: CaptureSource,
    pub(super) value: Value,
}

#[derive(Debug)]
enum CaptureSource {
    DispatchReceiver,
    Parameter(usize),
    Local(String),
}

impl Capture {
    pub(super) fn write(&self, out: &mut String, expected: Expected<'_>, parameters: &[ValueParameter], declaration: &str)
        -> Result<(), KotlinError>
    {
        if !self.value.accepts(expected) {
            return Err(invalid(declaration));
        }
        match &self.source {
            CaptureSource::DispatchReceiver => out.push_str("this"),
            CaptureSource::Parameter(index) => identifier(out, &parameters[*index].name, declaration)?,
            CaptureSource::Local(name) => out.push_str(name),
        }
        Ok(())
    }
}

impl Closure<'_> {
    pub(super) fn write(&self, out: &mut String, expected: Expected<'_>, parameters: &[ValueParameter], declaration: &str)
        -> Result<(), KotlinError>
    {
        if !matches!(expected, Expected::Type(ty, JvmType::Object(owner)) if owner == FUNCTION0
            && ty.simple_class("kotlin/Function0") && !ty.nullable
            && matches!(ty.arguments.as_slice(), [TypeArgument::Type(Variance::Invariant, returns)]
                if returns.simple_class("kotlin/Unit") && !returns.nullable && returns.arguments.is_empty()))
        {
            return Err(invalid(declaration));
        }
        out.push_str("{ ");
        for (capture, name, call) in &self.checks {
            out.push_str("kotlin.jvm.internal.Intrinsics.");
            out.push_str(call);
            out.push('(');
            capture.write(out, Expected::Reference, parameters, declaration)?;
            out.push_str(", ");
            super::write_string(out, name.encode_utf16());
            out.push_str("); ");
        }
        match &self.body {
            ClosureBody::Straight(statements) => {
                write_statements(statements, out, parameters, declaration)?;
                out.push_str("kotlin.Unit");
            }
            ClosureBody::While { condition, statements } => {
                out.push_str("while (");
                condition.write_at(out, Expected::Primitive(Primitive::Boolean), parameters, declaration, 0)?;
                out.push_str(") { ");
                write_statements(statements, out, parameters, declaration)?;
                out.push('}');
            }
        }
        out.push_str(" }");
        Ok(())
    }
}

fn write_statements(statements: &[Statement<'_>], out: &mut String, parameters: &[ValueParameter], declaration: &str)
    -> Result<(), KotlinError>
{
    for statement in statements {
        statement.write_exact_print(out, parameters, declaration)?;
        out.push_str("; ");
    }
    Ok(())
}

pub(super) fn lower<'a>(bytecode: &Bytecode<'a, '_>, raw: &str, arguments: &[u16], locals: &Locals<'_>,
    stack: &mut Vec<StackValue<'a>>, declaration: &str,
) -> Result<Expr<'a>, KotlinError> {
    let invalid = || invalid(declaration);
    let [sam, implementation, instantiated] = *arguments else { return Err(invalid()); };
    let pool = &bytecode.class.pool;
    let method_type = |index| match *pool.get(index)? {
        Constant::MethodType(descriptor) => Ok(pool.utf8(descriptor)?),
        _ => Err(invalid()),
    };
    let site = MethodDescriptor::parse(raw)?;
    if !matches!(&site.return_type, JvmType::Object(owner) if owner == FUNCTION0)
        || method_type(sam)? != "()Ljava/lang/Object;"
        || method_type(instantiated)? != "()Lkotlin/Unit;"
        || locals.captures.is_some() || locals.has_extension_receiver()
        || namespace_shadowed(locals)
    {
        return Err(invalid());
    }
    let Constant::MethodHandle { reference_kind: 6, reference_index } = *pool.get(implementation)? else {
        return Err(invalid());
    };
    if !matches!(pool.get(reference_index)?, Constant::Methodref { .. }) {
        return Err(invalid());
    }
    let (owner, name, raw) = pool.member_ref(reference_index)?;
    let descriptor = MethodDescriptor::parse(raw)?;
    if owner != bytecode.owner || descriptor.parameters != site.parameters
        || !matches!(&descriptor.return_type, JvmType::Object(name) if name == "kotlin/Unit")
        || locals.extension.as_ref().is_none_or(|context| context.members.functions.iter().any(|function| {
            function.signature.as_ref().is_some_and(|signature| signature.name == name && signature.descriptor == descriptor)
        }))
    {
        return Err(invalid());
    }
    let mut members = bytecode.class.methods.iter().filter(|method| {
        pool.utf8(method.name_index).is_ok_and(|candidate| candidate == name)
            && pool.utf8(method.descriptor_index).is_ok_and(|candidate| candidate == raw)
    });
    let method = members.next().filter(|member| {
        member.access_flags & !0x1000 == (0x0002 | STATIC | FINAL) && members.next().is_none()
    }).ok_or_else(invalid)?;
    let code = bytecode.code(method, declaration)?;
    let instructions = super::bytecode::decode(code.bytes)?;
    let [body @ .., unit, ret] = instructions.as_slice() else { return Err(invalid()); };
    if ret.opcode != 0xb0 || bytecode.reference(unit, 0xb2)? != Some(("kotlin/Unit", "INSTANCE", "Lkotlin/Unit;")) {
        return Err(invalid());
    }
    let first = stack.len().checked_sub(site.parameters.len()).ok_or_else(invalid)?;
    let captures = stack.drain(first..).zip(site.parameters).map(|(operand, jvm)| {
        let (source, ty) = match operand {
            StackValue::This if matches!(&jvm, JvmType::Object(owner) if owner == bytecode.owner) =>
                (CaptureSource::DispatchReceiver, kotlin_type(&bytecode.owner.replace('$', "."))),
            StackValue::Value(expr) => stable_capture(&expr, &jvm, locals, declaration)?.ok_or_else(invalid)?,
            _ => return Err(invalid()),
        };
        Ok(Rc::new(Capture { source, value: Value { ty, jvm } }))
    }).collect::<Result<Vec<_>, _>>()?;
    let mut helper = Locals::with_slots(&descriptor.parameters, false, None);
    helper.captures = Some(&captures);
    helper.closure_body = true;
    helper.templates.member = Some(method);
    helper.templates.properties = locals.templates.properties;
    let mut checks = Vec::new();
    let mut remaining = body;
    while let Some((slot, name, rest)) = bytecode.null_check(remaining)? {
        let parameter = helper.parameter(slot, 0x19).ok_or_else(invalid)?;
        let (_, call, _) = bytecode.reference(&remaining[2], 0xb8)?.ok_or_else(invalid)?;
        checks.push((Rc::clone(&captures[parameter]), name, call));
        remaining = rest;
    }
    let start = body.len() - remaining.len();
    let end = body.len();
    let body = if remaining.iter().any(|instruction| matches!(instruction.operand, Operand::Branch(_) | Operand::Switch { .. })) {
        while_body(bytecode, &instructions, start, end, &code, &helper, unit, declaration)?
    } else {
        ClosureBody::Straight(statements::lower_debug_range(bytecode, &instructions, start..end, &code, &helper, declaration)?)
    };
    let mut ty = kotlin_type("kotlin/Function0");
    ty.arguments.push(TypeArgument::Type(Variance::Invariant, kotlin_type("kotlin/Unit")));
    let value = Value { ty, jvm: site.return_type };
    Expr::new(ExprKind::Closure(Box::new(Closure { value, checks, body })), 1, declaration)
}

fn stable_capture(expr: &Expr<'_>, jvm: &JvmType, locals: &Locals<'_>, declaration: &str)
    -> Result<Option<(CaptureSource, Type)>, KotlinError>
{
    let source = match &expr.kind {
        ExprKind::Parameter { index, .. } => CaptureSource::Parameter(*index),
        ExprKind::Local(binding) if !binding.mutable => {
            let mut name = String::new();
            identifier(&mut name, &binding.name, declaration)?;
            CaptureSource::Local(name)
        }
        ExprKind::LoopLocal(binding) => {
            let ty = match (binding.element, jvm) {
                (Element::Primitive(actual), JvmType::Primitive(expected)) if actual == *expected => builtin_type(jvm),
                (Element::String, JvmType::Object(owner)) if owner == "java/lang/String" => builtin_type(jvm),
                (Element::Object, JvmType::Object(owner)) if owner == OBJECT => Some(any_nullable()),
                _ => None,
            };
            let Some(ty) = ty else { return Ok(None); };
            let mut name = String::new();
            binding.write(&mut name, declaration)?;
            return Ok(Some((CaptureSource::Local(name), ty)));
        }
        _ => return Ok(None),
    };
    Ok(expr.source_type(locals).and_then(|(ty, actual)| {
        (actual == jvm && exact_type(ty, jvm, false)).then(|| (source, ty.clone()))
    }))
}

fn while_body<'a, 'data>(bytecode: &Bytecode<'a, 'data>, instructions: &[Instruction], start: usize, end: usize,
    code: &super::Code<'data>, locals: &Locals<'_>, exit: &Instruction, declaration: &str,
) -> Result<ClosureBody<'a>, KotlinError> {
    let invalid = || invalid(declaration);
    let last = end.checked_sub(1).ok_or_else(invalid)?;
    let head = instructions.get(start).filter(|_| start < last).ok_or_else(invalid)?;
    if !matches!(instructions[last].opcode, 0xa7 | 0xc8) || instructions[last].operand != Operand::Branch(head.offset) {
        return Err(invalid());
    }
    let guard = (start..last).find(|&index| instructions[index].operand == Operand::Branch(exit.offset)).ok_or_else(invalid)?;
    let mut stack = Vec::new();
    let branches = instructions[start..guard].iter().position(|instruction| matches!(instruction.operand, Operand::Branch(_)));
    let prefix_end = branches.map_or(guard, |index| start + index);
    for instruction in &instructions[start..prefix_end] {
        bytecode.expression(instruction, locals, &mut stack, declaration)?;
    }
    let condition = if prefix_end == guard {
        logic::condition(instructions[guard].opcode, &mut stack, &[], declaration)?
    } else {
        let [branch, yes, skip, no, guard] = &instructions[prefix_end..=guard] else { return Err(invalid()); };
        if branch.operand != Operand::Branch(no.offset) || !matches!(skip.opcode, 0xa7 | 0xc8)
            || skip.operand != Operand::Branch(guard.offset) || !matches!(guard.opcode, 0x99 | 0x9a)
            || !matches!((yes.opcode, no.opcode), (0x03, 0x04) | (0x04, 0x03))
            || !matches!(stack.as_slice(), [StackValue::Value(expr)]
                if expr.primitive_hint(&[]) == Some(Primitive::Boolean))
        {
            return Err(invalid());
        }
        let condition = logic::condition(branch.opcode, &mut stack, &[], declaration)?;
        if (yes.opcode == 0x04) == (guard.opcode == 0x99) { condition }
        else { logic::negate(condition, declaration)? }
    };
    if !stack.is_empty() { return Err(invalid()); }
    let statements = statements::lower_debug_range(bytecode, instructions, guard + 1..last, code, locals, declaration)?;
    Ok(ClosureBody::While { condition, statements })
}

pub(super) fn ref_type(owner: &str) -> Option<Type> {
    match owner {
        INT_REF => Some(kotlin_type("kotlin/jvm/internal/Ref.IntRef")),
        OBJECT_REF => {
            let mut ty = kotlin_type("kotlin/jvm/internal/Ref.ObjectRef");
            ty.arguments.push(TypeArgument::Type(Variance::Invariant, any_nullable()));
            Some(ty)
        }
        _ => None,
    }
}

fn any_nullable() -> Type {
    let mut ty = kotlin_type("kotlin/Any");
    ty.nullable = true;
    ty
}

#[derive(Debug)]
pub(super) struct Field<'a> {
    receiver: Expr<'a>,
    name: &'a str,
    pub(super) value: Value,
}

impl Field<'_> {
    pub(super) fn write(&self, out: &mut String, expected: Expected<'_>, parameters: &[ValueParameter], declaration: &str)
        -> Result<(), KotlinError>
    {
        if !self.value.accepts(expected) { return Err(invalid(declaration)); }
        self.receiver.write_at(out, Expected::Reference, parameters, declaration, u8::MAX)?;
        out.push('.');
        identifier(out, self.name, declaration)
    }

    pub(super) fn assignment(&self, out: &mut String, expr: &Expr<'_>, parameters: &[ValueParameter], declaration: &str)
        -> Result<(), KotlinError>
    {
        let expected = Expected::Type(&self.value.ty, &self.value.jvm);
        self.write(out, expected, parameters, declaration)?;
        out.push_str(" = ");
        let rhs = if self.value.ty.class_id() == Some("kotlin/Any") { Expected::Reference } else { expected };
        expr.write_at(out, rhs, parameters, declaration, 0)
    }
}

fn field_value(bytecode: &Bytecode<'_, '_>, locals: &Locals<'_>, receiver: &Expr<'_>, owner: &str,
    name: &str, raw: &str,
) -> Result<Option<Value>, KotlinError> {
    let Some((ty, JvmType::Object(actual))) = receiver.source_type(locals) else { return Ok(None); };
    if owner != actual || ty.nullable { return Ok(None); }
    let value = match (owner, name, raw) {
        (INT_REF, "element", "I") if ref_type(owner).as_ref() == Some(ty) => {
            Value { ty: kotlin_type("kotlin/Int"), jvm: JvmType::Primitive(Primitive::Int) }
        }
        (OBJECT_REF, "element", "Ljava/lang/Object;") if ref_type(owner).as_ref() == Some(ty) => {
            Value { ty: any_nullable(), jvm: JvmType::Object(OBJECT.into()) }
        }
        _ if owner == bytecode.owner && matches!(&receiver.kind, ExprKind::Capture(capture)
            if matches!(capture.source, CaptureSource::DispatchReceiver)) => {
            // The class declaration's property plan validates the default
            // accessors against this exact backing field before rendering.
            let jvm = JvmType::parse(raw)?;
            let Some(property) = locals.templates.properties.iter().find(|property| {
                property.name == name && property.flags.modality() == Modality::Final
                    && property.mutable() && !property.delegated()
                    && !property.getter_flags.is_some_and(|flags| flags.has(6))
                    && !property.setter_flags.is_some_and(|flags| flags.has(6))
                    && property.signature.field.as_ref().is_some_and(|field| field.name == name && field.descriptor == jvm)
                    && exact_type(&property.ty, &jvm, false)
            }) else { return Ok(None); };
            Value { ty: property.ty.clone(), jvm }
        }
        _ => return Ok(None),
    };
    Ok(Some(value))
}

pub(super) fn store<'a>(bytecode: &Bytecode<'a, '_>, instruction: &Instruction, locals: &Locals<'_>,
    stack: &mut Vec<StackValue<'a>>, declaration: &str,
) -> Result<Option<(Field<'a>, Expr<'a>)>, KotlinError> {
    if !locals.closure_body { return Ok(None); }
    let Some((owner, name, raw)) = bytecode.reference(instruction, 0xb5)? else { return Ok(None); };
    let [StackValue::Value(receiver), StackValue::Value(rhs)] = stack.as_slice() else { return Err(invalid(declaration)); };
    let value = field_value(bytecode, locals, receiver, owner, name, raw)?.ok_or_else(|| invalid(declaration))?;
    if rhs.stack_load() != Some(load_opcode(&value.jvm)) { return Err(invalid(declaration)); }
    let rhs = pop_value(stack, declaration)?;
    let receiver = pop_value(stack, declaration)?;
    Ok(Some((Field { receiver, name, value }, rhs)))
}

#[derive(Debug)]
pub(super) struct Cast<'a> {
    operand: Expr<'a>,
    pub(super) value: Value,
}

impl Cast<'_> {
    pub(super) fn write(&self, out: &mut String, expected: Expected<'_>, parameters: &[ValueParameter], declaration: &str)
        -> Result<(), KotlinError>
    {
        if !self.value.accepts(expected) { return Err(invalid(declaration)); }
        out.push('(');
        self.operand.write_at(out, Expected::Reference, parameters, declaration, logic::RELATIONAL + 1)?;
        out.push_str(" as ");
        qualified(out, self.value.ty.class_id().unwrap(), declaration)?;
        out.push(')');
        Ok(())
    }
}

pub(super) fn expression<'a>(bytecode: &Bytecode<'a, '_>, instruction: &Instruction, locals: &Locals<'_>,
    stack: &mut Vec<StackValue<'a>>, declaration: &str,
) -> Result<bool, KotlinError> {
    if !locals.closure_body { return Ok(false); }
    if locals.captures.is_some() && super::invocations::lambda_text(bytecode, instruction, locals, stack, declaration)? {
        return Ok(true);
    }
    let kind = if let Some((owner, name, raw)) = bytecode.reference(instruction, 0xb4)? {
        let Some(StackValue::Value(receiver)) = stack.last() else { return Ok(false); };
        let Some(value) = field_value(bytecode, locals, receiver, owner, name, raw)? else { return Ok(false); };
        let receiver = pop_value(stack, declaration)?;
        let depth = receiver.depth + 1;
        (ExprKind::Field(Box::new(Field { receiver, name, value })), depth)
    } else if locals.captures.is_some() && instruction.opcode == 0xc0
        && let Operand::Constant(index) = instruction.operand
        && let owner @ ("java/lang/String" | "java/lang/CharSequence") = bytecode.class.pool.class_name(index)?
        && matches!(stack.last(), Some(StackValue::Value(expr)) if expr.stack_load() == Some(0x19))
    {
        let operand = pop_value(stack, declaration)?;
        let depth = operand.depth + 1;
        let jvm = JvmType::Object(owner.into());
        let ty = builtin_type(&jvm).unwrap();
        (ExprKind::Cast(Box::new(Cast { operand, value: Value { ty, jvm } })), depth)
    } else if bytecode.reference(instruction, 0xb6)? == Some(("java/lang/String", "length", "()I"))
        && matches!(stack.last(), Some(StackValue::Value(expr))
            if expr.source_type(locals).is_some_and(|(_, jvm)| matches!(jvm, JvmType::Object(owner) if owner == "java/lang/String")))
    {
        let receiver = pop_value(stack, declaration)?;
        let depth = receiver.depth + 1;
        (ExprKind::StringLength(Box::new(receiver)), depth)
    } else {
        return Ok(false);
    };
    stack.push(StackValue::Value(Expr::new(kind.0, kind.1, declaration)?));
    Ok(true)
}

pub(super) fn reserved(name: &str) -> bool {
    matches!(name, "kotlin" | "System" | "lambdaTextIsBlank" | "lambdaTextDrop")
        || name.starts_with("lambdaLocal") || name.starts_with("lambdaConcat")
}

pub(super) fn namespace_shadowed(locals: &Locals<'_>) -> bool {
    locals.templates.properties.iter().any(|property| reserved(&property.name))
        || locals.extension.as_ref().is_some_and(|context| {
            context.parameters.iter().any(|parameter| reserved(&parameter.name))
                || context.members.functions.iter().any(|function| reserved(&function.name))
        })
}

fn invalid(declaration: &str) -> KotlinError {
    KotlinError::unsupported(declaration, "unproven Kotlin lambda implementation or capture")
}
