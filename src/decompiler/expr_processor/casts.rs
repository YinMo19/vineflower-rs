//! Collapse consecutive casts with equal target types before rendering.

use crate::decompiler::{
    exps::{Expr, ExprKind, FunctionType},
    ir::{ExprId, Ir, StatId},
    stats::StatementKind,
};
use crate::engine::Cx;

pub(crate) fn canonicalize_casts(cx: &mut Cx, root: StatId) -> bool {
    let mut changed = false;
    while visit(cx, root) {
        changed = true;
    }
    changed
}

fn visit(cx: &mut Cx, stat: StatId) -> bool {
    let mut changed = false;
    for index in 0..cx.ir[stat].stats.len() {
        changed |= visit(cx, cx.ir[stat].stats[index]);
    }
    if matches!(cx.ir[stat].kind, StatementKind::BasicBlock { .. })
        && let Some(list) = cx.ir[stat].exprents
    {
        for index in 0..cx.ir[list].len() {
            let root = cx.ir[list][index];
            for expr in Expr::all_exprents(&cx.ir, root, true, true) {
                let Some((inner, target)) = cast(&cx.ir, expr) else {
                    continue;
                };
                let Some((value, nested_target)) = cast(&cx.ir, inner) else {
                    continue;
                };
                if Expr::expr_type(cx, target) == Expr::expr_type(cx, nested_target) {
                    Expr::replace(&mut cx.ir, expr, inner, value);
                    for source in [value, inner] {
                        let offsets = cx.ir[source].bytecode.clone();
                        Expr::add_offsets(&mut cx.ir, expr, offsets.as_ref());
                    }
                    changed = true;
                }
            }
        }
    }
    changed
}

fn cast(ir: &Ir, expr: ExprId) -> Option<(ExprId, ExprId)> {
    match &ir[expr].kind {
        ExprKind::Function {
            op: FunctionType::Cast,
            operands,
            ..
        } => Some((operands[0], operands[1])),
        _ => None,
    }
}
