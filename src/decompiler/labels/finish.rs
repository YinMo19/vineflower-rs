// Copyright 2000-2020 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Label rewrites used after declarations have been placed.

use rustc_hash::FxHashSet;

use super::is_direct_path;
use crate::decompiler::exps::{ExprKind, FunctionType};
use crate::decompiler::ir::{EdgeId, Ir, StatId};
use crate::decompiler::stats::{StatementKind, stat_edge::EdgeType};

pub(crate) fn hide_default_switch_edges(ir: &mut Ir, stat: StatId) -> bool {
    let mut changed = false;
    if let StatementKind::Switch(switch) = &ir[stat].kind
        && let Some(last) = switch.cases.last().map(|case| case.statement)
        && ir[last].exprents.is_some_and(|list| ir[list].is_empty())
        && !switch.case_values().flatten().flatten().any(|&expr| {
            matches!(
                ir[expr].kind,
                ExprKind::Function {
                    op: FunctionType::InstanceOf,
                    ..
                }
            )
        })
        && ir[last]
            .first_successor()
            .is_none_or(|edge| !ir[edge].explicit)
    {
        let StatementKind::Switch(switch) = &mut ir[stat].kind else {
            unreachable!();
        };
        switch.remove_trailing_default();
        changed = true;
    }

    for index in 0..ir[stat].stats.len() {
        changed |= hide_default_switch_edges(ir, ir[stat].stats[index]);
    }
    changed
}

/// The final label pass can leave the break's original loop destination in
/// place. Run it after all passes that require a consistent statement graph.
pub(crate) fn replace_continue_with_break(ir: &mut Ir, stat: StatId) -> bool {
    let mut changed =
        matches!(ir[stat].kind, StatementKind::Do(_)) && rewrite_loop_continues(ir, stat);
    for index in 0..ir[stat].stats.len() {
        changed |= replace_continue_with_break(ir, ir[stat].stats[index]);
    }
    changed
}

fn rewrite_loop_continues(ir: &mut Ir, stat: StatId) -> bool {
    let mut seen = FxHashSet::default();
    loop {
        let mut changed = false;
        for edge in stat.get_predecessor_edges(ir, EdgeType::Continue.mask()) {
            if seen.contains(&edge) || !ir[edge].explicit {
                continue;
            }

            let source = ir[edge].source;
            let minimum = minimum_continue_closure(ir, edge);
            if ir[edge].closure != Some(minimum) && !is_break_labeled(ir, source, minimum) {
                edge.change_type(ir, EdgeType::Break);
                ir[edge].labeled = false;
                minimum.add_labeled_edge(ir, edge);
                seen.insert(edge);
                changed = true;
            }

            let enclosing = max_unconditional_jump(ir, enclosing_shield(ir, source));
            if has_unconditional_jump(ir, enclosing)
                && enclosing_shield(ir, ir[enclosing].parent.expect("Missing loop parent"))
                    == minimum
            {
                edge.change_type(ir, EdgeType::Break);
                ir[edge].labeled = false;
                ir[edge].phantom_continue = true;
                enclosing.add_labeled_edge(ir, edge);
                seen.insert(edge);
                changed = true;
            }
        }

        if !changed {
            return !seen.is_empty();
        }
    }
}

fn is_shield(ir: &Ir, stat: StatId) -> bool {
    matches!(
        ir[stat].kind,
        StatementKind::Switch(_) | StatementKind::Do(_)
    )
}

fn is_break_labeled(ir: &Ir, source: StatId, closure: StatId) -> bool {
    if !is_shield(ir, closure) {
        return true;
    }
    let mut current = source;
    loop {
        let parent = ir[current].parent.expect("Missing break closure");
        if parent == closure {
            return false;
        }
        if is_shield(ir, parent) {
            return true;
        }
        current = parent;
    }
}

fn enclosing_shield(ir: &Ir, mut stat: StatId) -> StatId {
    while !is_shield(ir, stat) {
        let Some(parent) = ir[stat].parent else {
            break;
        };
        stat = parent;
    }
    stat
}

fn has_unconditional_jump(ir: &Ir, stat: StatId) -> bool {
    matches!(ir[stat].kind, StatementKind::Do(_))
        && !stat
            .get_successor_edges(ir, EdgeType::Break.mask())
            .is_empty()
}

fn max_unconditional_jump(ir: &Ir, mut stat: StatId) -> StatId {
    let mut last = stat;
    while has_unconditional_jump(ir, stat) {
        last = stat;
        stat = enclosing_shield(ir, ir[stat].parent.expect("Missing loop parent"));
    }
    last
}

fn minimum_continue_closure(ir: &Ir, edge: EdgeId) -> StatId {
    let edge = &ir[edge];
    let mut closure = edge.closure.expect("Continue has no closure");
    while let Some(&child) = ir[closure].stats.iter().find(|&&child| {
        child.contains_statement_strict(ir, edge.source)
            && is_direct_path(ir, child, edge.destination)
    }) {
        closure = child;
    }
    closure
}
