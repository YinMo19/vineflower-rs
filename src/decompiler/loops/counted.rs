//! Recover a counted for-loop from the initializer, loop condition and
//! trailing action at a while-loop's continue target.

use indexmap::IndexSet;

use super::{inherit_offsets, last_direct_data, preceding_data, remove_expr, used_before};
use crate::decompiler::exps::Expr;
use crate::decompiler::flow::flatten::build_direct_graph;
use crate::decompiler::ir::{ExprId, ExprKind, Ir, StatId};
use crate::decompiler::sforms::first_protected_range;
use crate::decompiler::stats::{
    LoopType, STATEDGE_ALL, Statement, StatementKind, stat_edge::EdgeType,
};
use crate::engine::{Cx, counter_container::CounterContainer};

pub(super) fn match_for(cx: &mut Cx, counters: &mut CounterContainer, root: StatId, stat: StatId) {
    let ir = &cx.ir;
    let body = ir[stat].first.unwrap();
    let Some(last) = last_direct_data(ir, body) else {
        return;
    };
    let tail = ir[last].exprents.unwrap();
    let Some(&action) = ir[tail].last() else {
        return;
    };
    if first_protected_range(ir, last)
        .is_some_and(|region| region == stat || stat.contains_statement_strict(ir, region))
    {
        return;
    }

    let single_target =
        ir[tail].len() == 1 && last.get_predecessor_edges(ir, STATEDGE_ALL).len() > 1;
    if !single_target
        && !matches!(
            ir[action].kind,
            ExprKind::Assignment { .. } | ExprKind::Function { .. }
        )
    {
        return;
    }
    let initializer = preceding_data(ir, stat, true).and_then(|prev| {
        let list = ir[prev].exprents?;
        let &expr = ir[list].last()?;
        matches!(ir[expr].kind, ExprKind::Assignment { .. }).then_some((list, expr))
    });

    if initializer.is_some() || single_target {
        if stat
            .get_predecessor_edges(ir, EdgeType::Continue.mask())
            .iter()
            .any(|&edge| ir[edge].source != last)
        {
            return;
        }
        let mut first = body;
        while matches!(ir[first].kind, StatementKind::Sequence) && ir[first].stats.len() == 1 {
            let Some(child) = ir[first].first else { break };
            first = child;
        }
        if matches!(ir[first].kind, StatementKind::BasicBlock { .. })
            && ir[ir[first].exprents.unwrap()].len() == 1
        {
            return;
        }
        if matches!(ir[action].kind, ExprKind::Exit { .. })
            || captures_final_local(ir, stat, action)
        {
            return;
        }
        if !action_uses_preexisting_slots(&mut cx.ir, root, stat, action) {
            return;
        }

        let StatementKind::Do(header) = cx.ir[stat].kind else {
            unreachable!()
        };
        if let Some((_, init)) = initializer
            && let ExprKind::Assignment { left, .. } = cx.ir[init].kind
            && let ExprKind::Variable(target) = &cx.ir[left].kind
        {
            let condition = header
                .condition(&cx.ir)
                .expect("While loop has no condition");
            if !Expr::contains_var(&cx.ir, condition, target.pair())
                && !Expr::contains_var(&cx.ir, action, target.pair())
            {
                return;
            }
        }
        stat.set_loop_type(&mut cx.ir, LoopType::For);
        if let Some((list, init)) = initializer {
            cx.ir[list].pop();
            if let Some(previous) = header.init(&cx.ir) {
                inherit_offsets(&mut cx.ir, init, previous);
            }
            stat.set_loop_init(&mut cx.ir, init);
        }
        remove_expr(cx, tail, action);
        if let Some(previous) = header.increment(&cx.ir) {
            inherit_offsets(&mut cx.ir, action, previous);
        }
        stat.set_loop_increment(&mut cx.ir, action);
    }

    if cx.ir[tail].is_empty() {
        if let Some(edge) = cx.ir[last].first_successor() {
            edge.remove(&mut cx.ir);
        }
        let parent = cx.ir[last].parent.unwrap();
        if !matches!(
            cx.ir[parent].kind,
            StatementKind::Catch { .. }
                | StatementKind::CatchAll { .. }
                | StatementKind::Synchronized { .. }
        ) {
            remove_last_empty(&mut cx.ir, counters, stat, last);
        }
    }
}

/// Captured locals assigned inside the loop cannot be read by a promoted action.
fn captures_final_local(ir: &Ir, stat: StatId, action: ExprId) -> bool {
    let mut statements = vec![stat];
    while let Some(stat) = statements.pop() {
        let headers;
        let exprs = if let Some(body) = ir[stat].exprents {
            ir[body].as_slice()
        } else {
            statements.extend(ir[stat].stats.iter().rev().copied());
            headers = stat.stat_exprents(ir);
            headers.as_slice()
        };
        for &expr in exprs {
            if Expr::all_exprents(ir, expr, true, true)
                .into_iter()
                .any(|id| {
                    matches!(ir[id].kind, ExprKind::Assignment { left, .. }
                    if matches!(&ir[left].kind, ExprKind::Variable(var) if var.effectively_final)
                        && Expr::is_var_referenced(ir, left, action, &[]))
                })
            {
                return true;
            }
        }
    }
    false
}

fn action_uses_preexisting_slots(ir: &mut Ir, root: StatId, stat: StatId, action: ExprId) -> bool {
    let slots: IndexSet<_> = Expr::all_exprents(ir, action, true, true)
        .into_iter()
        .filter_map(|id| match &ir[id].kind {
            ExprKind::Variable(var) => Some(var.index),
            _ => None,
        })
        .collect();
    if slots.is_empty() {
        return true;
    }
    // All the slot queries concern the same unmodified tree.
    let graph = build_direct_graph(ir, root);
    slots
        .into_iter()
        .all(|index| used_before(ir, &graph, stat, index))
}

pub(super) fn remove_last_empty(
    ir: &mut Ir,
    counters: &mut CounterContainer,
    stat: StatId,
    empty: StatId,
) {
    if ir[stat].first == Some(empty) {
        let new = Statement::new_empty_basic_block(ir, counters);
        stat.replace_statement(ir, empty, new);
        return;
    }
    for edge in empty.get_predecessor_edges(ir, STATEDGE_ALL) {
        edge.change_type(ir, EdgeType::Continue);
        edge.change_destination(ir, stat);
        stat.add_labeled_edge(ir, edge);
    }
    let parent = ir[empty].parent.unwrap();
    let id = ir[empty].id;
    ir[parent].stats.remove_with_key(&id);
    if let StatementKind::If(branch) = &mut ir[parent].kind {
        if branch.if_stat == Some(empty) {
            branch.if_stat = None;
        } else if branch.else_stat == Some(empty) {
            branch.else_stat = None;
        }
    }
}
