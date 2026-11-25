// Copyright 2000-2017 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Track the first write to an uninitialized declaration on each branch.

use crate::decompiler::{
    exps::{Expr, ExprKind},
    ir::{ExprId, Ir, StatId},
    stats::StatementKind,
    vars::{var_version_pair::VarVersionPair, versions::FinalType},
};
use rustc_hash::FxHashSet;

pub(super) fn set_non_final(ir: &mut Ir, root: StatId) {
    visit(ir, root, &mut FxHashSet::default());
}

fn visit(ir: &mut Ir, stat: StatId, uninitialized: &mut FxHashSet<VarVersionPair>) {
    if let Some(list) = ir[stat].exprents {
        for index in 0..ir[list].len() {
            let expr = ir[list][index];
            if let Some(var) = Expr::variable(ir, expr) {
                uninitialized.insert(var.pair());
            } else {
                write_expr(ir, expr, uninitialized);
            }
        }
    }

    match ir[stat].kind {
        StatementKind::Do(header) => {
            uninitialized.extend(ir[stat].var_definitions.iter().map(|&expr| {
                Expr::variable(ir, expr)
                    .expect("Expected a loop declaration")
                    .pair()
            }));
            for expr in [header.init(ir), header.increment(ir)]
                .into_iter()
                .flatten()
            {
                write_expr(ir, expr, uninitialized);
            }
        }
        StatementKind::If(branch)
            if let (Some(yes), Some(no)) = (branch.if_stat, branch.else_stat) =>
        {
            visit(ir, ir[stat].first.unwrap(), uninitialized);
            visit(ir, yes, &mut uninitialized.clone());
            visit(ir, no, uninitialized);
            return;
        }
        _ => {}
    }
    for index in 0..ir[stat].stats.len() {
        visit(ir, ir[stat].stats[index], uninitialized);
    }
}

fn write_expr(ir: &mut Ir, expr: ExprId, uninitialized: &mut FxHashSet<VarVersionPair>) {
    let target = match &ir[expr].kind {
        ExprKind::Assignment { left, .. } => Some(*left),
        ExprKind::Function { op, operands, .. } if op.is_inc_dec() => Some(operands[0]),
        _ => None,
    };
    if let Some(var) = target.and_then(|id| Expr::variable(ir, id))
        && !var.definition
        && !uninitialized.remove(&var.pair())
    {
        let owner = var.processor.expect("Missing variable processor");
        let pair = var.pair();
        ir[owner]
            .versions
            .final_vars
            .insert(pair, FinalType::NonFinal);
    }
    for child in Expr::children(ir, expr).collect::<Vec<_>>() {
        write_expr(ir, child, uninitialized);
    }
}
