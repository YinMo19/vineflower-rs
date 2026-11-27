//! Recognize or relocate increment and decrement expressions.

use super::{set_assignment_right, variable};
use crate::decompiler::exps::{Expr, ExprKind, FunctionType, delta_by_one, increment};
use crate::decompiler::ir::{ExprId, Ir};
use crate::engine::Cx;
use crate::engine::counter_container::CounterContainer;
use crate::types::VarType;

pub(super) fn prefix(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    first: ExprId,
) -> Option<ExprId> {
    let (left, function) = cx.ir[first].as_assignment()?;
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
    let Some((_, right)) = cx.ir[first].as_assignment() else {
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
        (cx.ir[first].as_assignment(), cx.ir[second].as_assignment())
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
