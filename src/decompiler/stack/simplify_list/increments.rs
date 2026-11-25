// Copyright 2000-2018 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Recognize or relocate increment and decrement expressions.

use super::{assignment, set_assignment_right, variable};
use crate::decompiler::exps::{ConstantValue, Expr, ExprKind, FunctionType};
use crate::decompiler::ir::{ExprId, Ir};
use crate::engine::Cx;
use crate::engine::counter_container::CounterContainer;
use crate::types::{CodeType, VarType};

pub(super) fn prefix(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    first: ExprId,
) -> Option<ExprId> {
    let (left, function) = assignment(&cx.ir, first)?;
    let (operand, add) = delta_by_one(&cx.ir, function)?;
    if variable(&cx.ir, left).is_some() || !Expr::equals(cx, left, operand) {
        return None;
    }
    let ty = Expr::expr_type(cx, operand);
    let op = if add {
        FunctionType::Ppi
    } else {
        FunctionType::Mmi
    };
    Some(increment(cx, counters, function, op, operand, ty))
}

pub(super) fn postfix(cx: &mut Cx, first: ExprId, second: ExprId) -> bool {
    let Some((_, right)) = assignment(&cx.ir, first) else {
        return false;
    };
    let ExprKind::Function { op, operands, .. } = &cx.ir[second].kind else {
        return false;
    };
    let postfix = match op {
        FunctionType::Ppi => FunctionType::Ipp,
        FunctionType::Mmi => FunctionType::Imm,
        _ => return false,
    };
    if !Expr::equals(cx, operands[0], right) {
        return false;
    }
    let ExprKind::Function { op, .. } = &mut cx.ir[second].kind else {
        unreachable!()
    };
    *op = postfix;
    set_assignment_right(&mut cx.ir, first, second);
    true
}

pub(super) fn postfix_assignment(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    first: ExprId,
    second: ExprId,
) -> bool {
    let (Some((left, right)), Some((target, function))) =
        (assignment(&cx.ir, first), assignment(&cx.ir, second))
    else {
        return false;
    };
    let Some((operand, add)) = delta_by_one(&cx.ir, function) else {
        return false;
    };
    if !Expr::equals(cx, left, operand)
        || !Expr::equals(cx, right, target)
        || Expr::usage(&cx.ir, left) & Expr::MULTIPLE_USES == 0
    {
        return false;
    }
    let op = if add {
        FunctionType::Ipp
    } else {
        FunctionType::Imm
    };
    let value = increment(cx, counters, function, op, right, VarType::VARTYPE_INT);
    set_assignment_right(&mut cx.ir, first, value);
    true
}

pub(super) fn inline_prefix(ir: &mut Ir, current: ExprId, next: ExprId) -> bool {
    let ExprKind::Function {
        op: FunctionType::Ppi | FunctionType::Mmi,
        operands,
        ..
    } = &ir[current].kind
    else {
        return false;
    };
    let Some(var) = variable(ir, operands[0]) else {
        return false;
    };
    if let Some((parent, read)) = first_valid_use(ir, var.index, var.version, next) {
        Expr::replace(ir, parent, read, current);
        true
    } else {
        false
    }
}

fn first_valid_use(ir: &Ir, index: i32, version: i32, next: ExprId) -> Option<(ExprId, ExprId)> {
    let mut pending = vec![(None, next)];
    while let Some((parent, expr)) = pending.pop() {
        if let Some(parent) = parent
            && variable(ir, expr).is_some_and(|v| v.index == index && v.version == version)
        {
            return Some((parent, expr));
        }
        if matches!(
            ir[expr].kind,
            ExprKind::Function {
                op: FunctionType::Ppi
                    | FunctionType::Mmi
                    | FunctionType::Ipp
                    | FunctionType::Imm
                    | FunctionType::BoolOr
                    | FunctionType::BoolAnd
                    | FunctionType::Ternary
                    | FunctionType::Sub
                    | FunctionType::Div,
                ..
            }
        ) {
            return None;
        }

        let start = pending.len();
        pending.extend(Expr::children(ir, expr).filter_map(|child| {
            let writes_target = matches!(ir[expr].kind, ExprKind::Assignment { left, .. } if child == left)
                && variable(ir, child).is_some_and(|v| v.index == index);
            (!writes_target).then_some((Some(expr), child))
        }));
        pending[start..].reverse();
    }
    None
}

fn delta_by_one(ir: &Ir, func: ExprId) -> Option<(ExprId, bool)> {
    let ExprKind::Function { op, operands, .. } = &ir[func].kind else {
        return None;
    };
    let add = match op {
        FunctionType::Add => true,
        FunctionType::Sub => false,
        _ => return None,
    };
    let (mut operand, mut constant) = (operands[0], operands[1]);
    if add
        && !matches!(ir[constant].kind, ExprKind::Constant { .. })
        && matches!(ir[operand].kind, ExprKind::Constant { .. })
    {
        std::mem::swap(&mut operand, &mut constant);
    }
    has_value_one(ir, constant).then_some((operand, add))
}

fn has_value_one(ir: &Ir, constant: ExprId) -> bool {
    let ExprKind::Constant {
        var_type, value, ..
    } = &ir[constant].kind
    else {
        return false;
    };
    matches!(
        (var_type.ty, value),
        (
            CodeType::Boolean
                | CodeType::Byte
                | CodeType::Bytechar
                | CodeType::Char
                | CodeType::Short
                | CodeType::Shortchar
                | CodeType::Int,
            ConstantValue::Integer(1),
        ) | (CodeType::Long, ConstantValue::Long(1))
            | (CodeType::Double, ConstantValue::Double(1.0))
            | (CodeType::Float, ConstantValue::Float(1.0))
    )
}

fn increment(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    original: ExprId,
    op: FunctionType,
    operand: ExprId,
    ty: VarType,
) -> ExprId {
    let offsets = cx.ir[original].bytecode.clone();
    let id = Expr::function(&mut cx.ir, counters, op, vec![operand], offsets);
    let ExprKind::Function { implicit_type, .. } = &mut cx.ir[id].kind else {
        unreachable!()
    };
    *implicit_type = Some(Box::new(ty));
    id
}
