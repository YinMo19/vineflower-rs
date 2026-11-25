// Copyright 2000-2018 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Arithmetic expressions used to reconstruct JVM increment and decrement idioms.

use super::{ConstantValue, Expr, ExprKind, FunctionType};
use crate::decompiler::ir::{ExprId, Ir};
use crate::engine::{Cx, counter_container::CounterContainer};
use crate::types::{CodeType, VarType};

pub(crate) fn delta_by_one(ir: &Ir, func: ExprId) -> Option<(ExprId, bool)> {
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

pub(crate) fn increment(
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
