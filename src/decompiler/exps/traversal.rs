// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Expression order used by the statement and SSA passes.

use crate::decompiler::ir::{ExprId, ExprListId, Ir, StatId};
use crate::decompiler::stats::{LoopType, StatementKind};

use super::{Expr, ExprKind};

impl Expr {
    /// The immediate expressions in `Exprent.getAllExprents()` order.
    /// Aliased expressions are yielded at each position where they occur.
    pub fn children(ir: &Ir, expr: ExprId) -> impl Iterator<Item = ExprId> + '_ {
        let (leading, lists): ([Option<ExprId>; 2], [&[ExprId]; 2]) = match &ir[expr].kind {
            ExprKind::Assert { condition, message } => ([*condition, *message], [&[], &[]]),
            ExprKind::Constant { .. } | ExprKind::Variable(_) => ([None, None], [&[], &[]]),
            ExprKind::Assignment { left, right, .. } => ([Some(*left), Some(*right)], [&[], &[]]),
            ExprKind::Array { array, index, .. } => ([Some(*array), Some(*index)], [&[], &[]]),
            ExprKind::Field(field) => ([field.instance, None], [&[], &[]]),
            ExprKind::Invocation(invoke) => ([invoke.instance, None], [&invoke.parameters, &[]]),
            ExprKind::Function { operands, .. } => ([None, None], [operands, &[]]),
            ExprKind::New {
                new_type,
                dimensions,
                array_elements,
                ..
            } if new_type.array_dim != 0 => ([None, None], [dimensions, array_elements]),
            ExprKind::New {
                constructor: Some(constructor),
                ..
            } => {
                // An object allocation exposes the constructor's receiver and arguments.
                let ExprKind::Invocation(invoke) = &ir[*constructor].kind else {
                    unreachable!("NewExprent constructor must be an invocation");
                };
                ([invoke.instance, None], [&invoke.parameters, &[]])
            }
            ExprKind::New {
                constructor: None, ..
            } => ([None, None], [&[], &[]]),
            ExprKind::Exit { value, .. } => ([*value, None], [&[], &[]]),
            ExprKind::Monitor { value, .. } | ExprKind::SwitchHead { value, .. } => {
                ([Some(*value), None], [&[], &[]])
            }
            ExprKind::If { condition } => ([Some(*condition), None], [&[], &[]]),
        };
        leading
            .into_iter()
            .flatten()
            .chain(lists.into_iter().flatten().copied())
    }

    /// `Exprent.getAllExprents(recursive, self)`.
    pub fn all_exprents(ir: &Ir, expr: ExprId, recursive: bool, include_self: bool) -> Vec<ExprId> {
        let mut result = Vec::new();
        Self::append_exprents(ir, expr, recursive, &mut result);
        if include_self {
            result.push(expr);
        }
        result
    }

    /// Appends the direct children first, then visits their descendants in
    /// reverse child order, as in `Exprent.getAllExprents`.
    pub(crate) fn append_exprents(ir: &Ir, expr: ExprId, recursive: bool, out: &mut Vec<ExprId>) {
        let start = out.len();
        out.extend(Self::children(ir, expr));
        if recursive {
            for index in (start..out.len()).rev() {
                Self::append_exprents(ir, out[index], true, out);
            }
        }
    }
}

impl StatId {
    /// `Statement.getStatExprents`, including compound statement headers and
    /// catch resources. A statement's body is held separately in `exprents`.
    pub fn stat_exprents(self, ir: &Ir) -> Vec<ExprId> {
        let list = |id: Option<ExprListId>| id.map_or(&[][..], |id| ir[id].as_slice());
        match &ir[self].kind {
            StatementKind::Do(loop_stat) => match loop_stat.ty {
                LoopType::Infinite => Vec::new(),
                LoopType::While | LoopType::DoWhile => {
                    vec![loop_stat.condition(ir).expect("Loop condition is missing")]
                }
                LoopType::For => loop_stat
                    .init(ir)
                    .into_iter()
                    .chain([
                        loop_stat.condition(ir).expect("Loop condition is missing"),
                        loop_stat.increment(ir).expect("Loop increment is missing"),
                    ])
                    .collect(),
                LoopType::ForEach => vec![
                    loop_stat.init(ir).expect("Foreach variable is missing"),
                    loop_stat.increment(ir).expect("Foreach iterable is missing"),
                ],
            },
            StatementKind::If(branch) => list(branch.head_exprents).to_vec(),
            StatementKind::Synchronized { head_exprents, .. } => list(*head_exprents).to_vec(),
            StatementKind::Catch {
                resources, vars, ..
            } => list(*resources).iter().chain(vars).copied().collect(),
            StatementKind::Switch(switch) => list(switch.head_exprents)
                .iter()
                .copied()
                .chain(switch.case_guards.iter().flatten().copied())
                .chain(
                    switch
                        .cases
                        .iter()
                        .flat_map(|case| case.values.iter().flatten().copied()),
                )
                .collect(),
            _ => Vec::new(),
        }
    }
}
