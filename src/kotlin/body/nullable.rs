// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.

//! Recover the duplicate-and-test shape without interpreting `dup` as a
//! duplicate Kotlin expression. The branch consumes the test copy; its two
//! successors must either consume or forward the original operand exactly once.

use std::ops::Range;

use super::{
    Bytecode, Expected, Expr, ExprKind, Instruction, JvmType, KotlinError, Literal, Locals, Operand,
    Primitive, StackValue, Type, ValueParameter,
    extensions::{Value, exact_type},
    invocations::{self, GuardedMember},
    load_opcode, local_store, pop_value, return_opcode,
};

pub(super) enum Plan<'a> {
    Expression(Expr<'a>),
    Statements { expression: Expr<'a>, join: usize },
}

#[derive(Debug)]
pub(super) struct Expression<'a> {
    receiver: Expr<'a>,
    source: Value,
    call: Option<GuardedMember>,
    fallback: Option<Fallback<'a>>,
    result: Value,
}

#[derive(Debug)]
enum Fallback<'a> {
    Value(Expr<'a>, Option<Value>),
    Throw(Expr<'a>),
    Return(Option<(Expr<'a>, Value)>),
}

impl<'a> Expression<'a> {
    pub(super) fn result(&self) -> &Value {
        &self.result
    }

    fn has_early_return(&self) -> bool {
        match &self.fallback {
            Some(Fallback::Return(_)) => true,
            Some(Fallback::Value(Expr { kind: ExprKind::Nullable(next), .. }, _)) => {
                next.has_early_return()
            }
            _ => false,
        }
    }

    pub(super) fn write(
        &self,
        out: &mut String,
        expected: Expected<'_>,
        parameters: &[ValueParameter],
        declaration: &str,
        binding: u8,
    ) -> Result<(), KotlinError> {
        if !self.result.accepts(expected) {
            return Err(invalid(declaration));
        }
        let parens = self.fallback.is_some() && binding != 0;
        if parens {
            out.push('(');
        }
        self.receiver.write_at(
            out, Expected::Type(&self.source.ty, &self.source.jvm), parameters, declaration, u8::MAX,
        )?;
        if let Some(call) = self.call {
            call.write(out);
        }
        if let Some(fallback) = &self.fallback {
            out.push_str(" ?: ");
            match fallback {
                Fallback::Value(expr, source) => write_value(
                    expr, source.as_ref().unwrap_or(&self.result), out, parameters, declaration,
                )?,
                Fallback::Throw(expr) => {
                    out.push_str("throw ");
                    expr.write_at(out, Expected::Reference, parameters, declaration, 0)?;
                }
                Fallback::Return(value) => {
                    out.push_str("return");
                    if let Some((expr, expected)) = value {
                        out.push(' ');
                        write_value(expr, expected, out, parameters, declaration)?;
                    }
                }
            }
        }
        if parens {
            out.push(')');
        }
        Ok(())
    }

    fn into_expr(self, declaration: &str) -> Result<Expr<'a>, KotlinError> {
        let left = self.receiver.depth + u8::from(self.call.is_some());
        let right = match &self.fallback {
            Some(Fallback::Value(expr, _) | Fallback::Throw(expr) | Fallback::Return(Some((expr, _)))) => expr.depth,
            _ => 0,
        };
        Expr::new(ExprKind::Nullable(Box::new(self)), left.max(right) + 1, declaration)
    }
}

pub(super) fn elided_trace(instruction: &Instruction) -> bool {
    matches!(instruction.opcode, 0x59 | 0x57 | 0xa7 | 0xc8)
}

pub(super) fn lower<'a>(
    bytecode: &Bytecode<'a, '_>,
    instructions: &[Instruction],
    start: usize,
    branch: usize,
    locals: &Locals<'_>,
    returning: (&Type, &JvmType),
    declaration: &str,
) -> Result<Option<Plan<'a>>, KotlinError> {
    let lowering = Lowering { bytecode, instructions, locals, returning, declaration };
    let Some(guard) = lowering.guard(start, branch, instructions.len())? else { return Ok(None); };
    let (join, last) = (guard.join, instructions.len() - 1);
    let store = local_store(&instructions[join]);
    let final_return = join == last && instructions[join].opcode == return_opcode(returning.1);
    if !final_return && store.is_none() {
        return Err(invalid(declaration));
    }
    let target = final_return.then_some(returning);
    let expression = lowering.expression(start, guard, target, 0)?;
    if let Some((opcode, _)) = store
        && (expression.result.jvm == JvmType::Void
            || load_opcode(&expression.result.jvm) + 0x21 != opcode)
    {
        return Err(invalid(declaration));
    }
    let needs_block = !final_return || *returning.1 == JvmType::Void || expression.has_early_return();
    let expression = expression.into_expr(declaration)?;
    Ok(Some(if needs_block {
        Plan::Statements { expression, join }
    } else {
        Plan::Expression(expression)
    }))
}

struct Guard {
    duplicate: usize,
    present: Range<usize>,
    absent: Range<usize>,
    join: usize,
}

struct Lowering<'b, 'a, 'data> {
    bytecode: &'b Bytecode<'a, 'data>,
    instructions: &'b [Instruction],
    locals: &'b Locals<'b>,
    returning: (&'b Type, &'b JvmType),
    declaration: &'b str,
}

impl<'a> Lowering<'_, 'a, '_> {
    fn guard(&self, start: usize, branch: usize, end: usize) -> Result<Option<Guard>, KotlinError> {
        let code = self.instructions;
        let Operand::Branch(target) = code[branch].operand else { return Ok(None); };
        if branch == start || code[branch - 1].opcode != 0x59 || !matches!(code[branch].opcode, 0xc6 | 0xc7) {
            return Ok(None);
        }
        let invalid = || invalid(self.declaration);
        let target = self.index(target)?;
        let (present, absent, join) = if code[branch].opcode == 0xc7 {
            // ifnonnull retains the unmodified reference at the join.
            (branch + 1..branch + 1, branch + 1, target)
        } else {
            if target <= branch + 1 || target >= end {
                return Err(invalid());
            }
            let Operand::Branch(join) = code[target - 1].operand else { return Err(invalid()); };
            if !matches!(code[target - 1].opcode, 0xa7 | 0xc8) {
                return Err(invalid());
            }
            (branch + 1..target - 1, target, self.index(join)?)
        };
        if join > end || join <= absent || code[absent].opcode != 0x57 {
            return Err(invalid());
        }
        Ok(Some(Guard { duplicate: branch - 1, present, absent: absent + 1..join, join }))
    }

    fn expression(
        &self,
        start: usize,
        guard: Guard,
        target: Option<(&Type, &JvmType)>,
        depth: u8,
    ) -> Result<Expression<'a>, KotlinError> {
        let invalid = || invalid(self.declaration);
        if depth >= 64 || start == guard.duplicate || guard.join >= self.instructions.len() {
            return Err(invalid());
        }
        let receiver = self.one_value(start..guard.duplicate)?;
        let (ty, jvm) = receiver.source_type(self.locals).ok_or_else(invalid)?;
        if !ty.nullable || load_opcode(jvm) != 0x19 || receiver.stack_load() != Some(0x19) {
            return Err(invalid());
        }
        let present_code = &self.instructions[guard.present];
        let (call, result) = if let Some((result_ty, JvmType::Void)) = target {
            let [call] = present_code else { return Err(invalid()); };
            let call = invocations::guarded_member(self.bytecode, call, ty, jvm, self.declaration)?;
            (Some(call), Value { ty: result_ty.clone(), jvm: JvmType::Void })
        } else {
            if !exact_type(ty, jvm, false) {
                return Err(invalid());
            }
            let unboxed = self.unbox(ty, jvm, present_code)?.map(JvmType::Primitive);
            let actual = unboxed.as_ref().unwrap_or(jvm);
            let result = if let Some((expected, descriptor)) = target {
                if !assignable(ty, actual, expected, descriptor, true) {
                    return Err(invalid());
                }
                Value { ty: expected.clone(), jvm: descriptor.clone() }
            } else {
                let mut projected = ty.clone();
                projected.nullable = false;
                projected.abbreviated = None;
                Value { ty: projected, jvm: unboxed.unwrap_or_else(|| jvm.clone()) }
            };
            (None, result)
        };
        let source = Value { ty: ty.clone(), jvm: jvm.clone() };
        let fallback = self.fallback(guard.absent, &result, depth)?;
        if result.jvm != JvmType::Void && fallback.is_none() {
            return Err(invalid());
        }
        Ok(Expression { receiver, source, call, fallback, result })
    }

    fn unbox(&self, ty: &Type, jvm: &JvmType, code: &[Instruction]) -> Result<Option<Primitive>, KotlinError> {
        let invalid = || invalid(self.declaration);
        match code {
            [] => Ok(None),
            [unbox] => {
                let (primitive, owner, name, descriptor) = match ty.class_id() {
                    Some("kotlin/Boolean") => (Primitive::Boolean, "java/lang/Boolean", "booleanValue", "()Z"),
                    Some("kotlin/Byte") => (Primitive::Byte, "java/lang/Byte", "byteValue", "()B"),
                    Some("kotlin/Char") => (Primitive::Char, "java/lang/Character", "charValue", "()C"),
                    Some("kotlin/Short") => (Primitive::Short, "java/lang/Short", "shortValue", "()S"),
                    Some("kotlin/Int") => (Primitive::Int, "java/lang/Integer", "intValue", "()I"),
                    Some("kotlin/Long") => (Primitive::Long, "java/lang/Long", "longValue", "()J"),
                    Some("kotlin/Float") => (Primitive::Float, "java/lang/Float", "floatValue", "()F"),
                    Some("kotlin/Double") => (Primitive::Double, "java/lang/Double", "doubleValue", "()D"),
                    _ => return Err(invalid()),
                };
                if !matches!(jvm, JvmType::Object(wrapper) if wrapper == owner)
                    || !matches!(unbox.operand, Operand::Constant(index)
                        if matches!(self.bytecode.class.pool.get(index)?, super::Constant::Methodref { .. }))
                    || self.bytecode.reference(unbox, 0xb6)? != Some((owner, name, descriptor))
                {
                    return Err(invalid());
                }
                Ok(Some(primitive))
            }
            _ => Err(invalid()),
        }
    }

    fn fallback(&self, range: Range<usize>, result: &Value, depth: u8) -> Result<Option<Fallback<'a>>, KotlinError> {
        let invalid = || invalid(self.declaration);
        if range.is_empty() {
            return Ok(None);
        }
        let transfer = range.clone().find(|&index| {
            matches!(self.instructions[index].operand, Operand::Branch(_) | Operand::Switch { .. })
        });
        if let Some(branch) = transfer
            && let Some(guard) = self.guard(range.start, branch, range.end)?
        {
            if guard.join != range.end || result.jvm == JvmType::Void {
                return Err(invalid());
            }
            let value = self.expression(range.start, guard, Some((&result.ty, &result.jvm)), depth + 1)?;
            return Ok(Some(Fallback::Value(value.into_expr(self.declaration)?, None)));
        }
        let last = &self.instructions[range.end - 1];
        let fallback = match last.opcode {
            0xbf => {
                let thrown = self.one_value(range.start..range.end - 1)?;
                if !thrown.source_type(self.locals).is_some_and(|(ty, jvm)| {
                    !ty.nullable && invocations::throwable_owner(ty, jvm).is_some()
                }) {
                    return Err(invalid());
                }
                Fallback::Throw(thrown)
            }
            0xac..=0xb1 if last.opcode == return_opcode(self.returning.1) => {
                let (ty, jvm) = self.returning;
                if *jvm == JvmType::Void {
                    if range.len() != 1 { return Err(invalid()); }
                    Fallback::Return(None)
                } else {
                    let value = self.one_value(range.start..range.end - 1)?;
                    if value.stack_load() != Some(load_opcode(jvm)) { return Err(invalid()); }
                    let rendered = self.value_type(&value, ty, jvm)?;
                    Fallback::Return(Some((value, rendered.unwrap_or_else(|| Value { ty: ty.clone(), jvm: jvm.clone() }))))
                }
            }
            _ if result.jvm != JvmType::Void => {
                let value = self.one_value(range)?;
                if value.stack_load() != Some(load_opcode(&result.jvm)) { return Err(invalid()); }
                let rendered = self.value_type(&value, &result.ty, &result.jvm)?;
                Fallback::Value(value, rendered)
            }
            _ => return Err(invalid()),
        };
        Ok(Some(fallback))
    }

    fn value_type(&self, value: &Expr<'_>, expected: &Type, descriptor: &JvmType) -> Result<Option<Value>, KotlinError> {
        if let Some((ty, jvm)) = value.source_type(self.locals) {
            if !assignable(ty, jvm, expected, descriptor, false) {
                return Err(invalid(self.declaration));
            }
            if ty != expected || jvm != descriptor {
                return Ok(Some(Value { ty: ty.clone(), jvm: jvm.clone() }));
            }
        }
        Ok(None)
    }

    fn one_value(&self, range: Range<usize>) -> Result<Expr<'a>, KotlinError> {
        let mut stack = Vec::new();
        for instruction in &self.instructions[range] {
            self.bytecode.expression(instruction, self.locals, &mut stack, self.declaration)?;
        }
        if !matches!(stack.as_slice(), [StackValue::Value(_)]) {
            return Err(invalid(self.declaration));
        }
        pop_value(&mut stack, self.declaration)
    }

    fn index(&self, offset: u32) -> Result<usize, KotlinError> {
        self.instructions.binary_search_by_key(&offset, |instruction| instruction.offset)
            .map_err(|_| invalid(self.declaration))
    }
}

fn write_value(
    value: &Expr<'_>,
    result: &Value,
    out: &mut String,
    parameters: &[ValueParameter],
    declaration: &str,
) -> Result<(), KotlinError> {
    let expected = if any_type(&result.ty, &result.jvm)
        && matches!(value.kind, ExprKind::Literal(Literal::String(_)) | ExprKind::Template(_) | ExprKind::Boxed(..))
    {
        Expected::Reference
    } else {
        Expected::Type(&result.ty, &result.jvm)
    };
    value.write_at(out, expected, parameters, declaration, 0)
}

fn any_type(ty: &Type, jvm: &JvmType) -> bool {
    ty.class_id() == Some("kotlin/Any") && matches!(jvm, JvmType::Object(owner) if owner == "java/lang/Object")
}

fn assignable(ty: &Type, jvm: &JvmType, expected: &Type, descriptor: &JvmType, guarded: bool) -> bool {
    (guarded || !ty.nullable || expected.nullable)
        && ((jvm == descriptor
            && ty.classifier == expected.classifier
            && ty.arguments == expected.arguments
            && ty.outer == expected.outer
            && ty.flexible == expected.flexible
            && ty.raw == expected.raw
            && ty.suspend == expected.suspend
            && ty.definitely_not_null == expected.definitely_not_null)
            || (any_type(expected, descriptor) && load_opcode(jvm) == 0x19))
}

fn invalid(declaration: &str) -> KotlinError {
    KotlinError::unsupported(declaration, "unproven Kotlin nullable control flow")
}
