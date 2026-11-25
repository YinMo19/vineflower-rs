// SPDX-License-Identifier: Apache-2.0

//! Narrow record components when a merged condition binds a stronger type.

use std::io;

use super::{header, operands};
use crate::decompiler::exps::{Expr, ExprKind, FunctionType};
use crate::decompiler::ir::{ExprId, StatId};
use crate::decompiler::stats::StatementKind;
use crate::engine::Cx;

pub(super) fn pattern_types(cx: &mut Cx, stat: StatId) -> io::Result<()> {
    for i in 0..cx.ir[stat].stats.len() {
        pattern_types(cx, cx.ir[stat].stats[i])?;
    }
    if let StatementKind::If(branch) = cx.ir[stat].kind {
        let (head, condition) = header(&cx.ir, branch);
        improve(cx, head, condition, branch.if_stat)?;
    }
    Ok(())
}

fn improve(cx: &mut Cx, parent: ExprId, expr: ExprId, body: Option<StatId>) -> io::Result<()> {
    for current in Expr::all_exprents(&cx.ir, expr, false, true) {
        if current != expr {
            improve(cx, expr, current, body)?;
        }
        let Some(&[base, _]) = operands(&cx.ir, current, FunctionType::BoolAnd) else {
            continue;
        };
        let Some(&pattern) =
            operands(&cx.ir, base, FunctionType::InstanceOf).and_then(|ops| ops.get(2))
        else {
            continue;
        };
        let ExprKind::Pattern(data) = &cx.ir[pattern].kind else {
            continue;
        };
        let children = data.children.clone();
        for (index, var) in children.into_iter().enumerate() {
            if Expr::variable(&cx.ir, var).is_none() {
                continue;
            }
            let body = body.ok_or_else(|| {
                io::Error::new(
                    io::ErrorKind::InvalidData,
                    "Record pattern has no true branch",
                )
            })?;
            if !Expr::is_var_referenced_in_stat(&cx.ir, var, body, &[]) {
                narrow_component(cx, parent, pattern, index, var);
            }
        }
    }
    Ok(())
}

fn narrow_component(cx: &mut Cx, parent: ExprId, pattern: ExprId, index: usize, var: ExprId) {
    for expr in Expr::all_exprents(&cx.ir, parent, true, true) {
        for child in Expr::all_exprents(&cx.ir, expr, false, false) {
            let Some(&[left, right]) = operands(&cx.ir, child, FunctionType::BoolAnd) else {
                continue;
            };
            for (test, other) in [(left, right), (right, left)] {
                if let Some(&[source, target, binding, ..]) =
                    operands(&cx.ir, test, FunctionType::InstanceOf)
                    && Expr::equals(cx, source, var)
                {
                    let bound = Expr::expr_type(cx, target);
                    let ExprKind::Pattern(data) = &mut cx.ir[pattern].kind else {
                        unreachable!()
                    };
                    data.children[index] = binding;
                    data.bound_types[index] = Some(bound);
                    Expr::replace(&mut cx.ir, expr, child, other);
                    return;
                }
            }
        }
    }
}
