// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! EliminateLoopsHelper and its break-closure analysis.

use std::io;

use rustc_hash::{FxHashMap, FxHashSet};

use crate::decompiler::decompose::finish::condense_sequences;
use crate::decompiler::ir::{EdgeId, Ir, StatId};
use crate::decompiler::stack::simplify_statement_without_ssa;
use crate::decompiler::stats::{DoStatement, LoopType, StatementKind, stat_edge::EdgeType};
use crate::engine::{Cx, counter_container::CounterContainer};
use crate::structs::StructClass;

pub(crate) fn eliminate(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    root: StatId,
    class: &StructClass,
) -> io::Result<bool> {
    let cx = &mut *cx.enter_method(counters);
    if !eliminate_one(&mut cx.ir, root) {
        return Ok(false);
    }

    condense_sequences(cx, counters, root);
    let mut reordered = FxHashSet::default();
    while simplify_statement_without_ssa(cx, counters, root, &mut reordered, class)? {
        condense_sequences(cx, counters, root);
    }
    Ok(true)
}

fn eliminate_one(ir: &mut Ir, stat: StatId) -> bool {
    for index in 0..ir[stat].stats.len() {
        if eliminate_one(ir, ir[stat].stats[index]) {
            return true;
        }
    }

    matches!(
        ir[stat].kind,
        StatementKind::Do(DoStatement {
            ty: LoopType::Infinite,
            ..
        })
    ) && eliminate_redundant(ir, stat)
}

fn eliminate_redundant(ir: &mut Ir, loop_stat: StatId) -> bool {
    let Some(parent_loop) = std::iter::successors(ir[loop_stat].parent, |&stat| ir[stat].parent)
        .find(|&stat| matches!(ir[stat].kind, StatementKind::Do(_)))
    else {
        return false;
    };
    if parent_loop.get_basic_head(ir) != loop_stat.get_basic_head(ir) {
        return false;
    }

    let body = ir[loop_stat].first.unwrap();
    let first_edge = ir[body].first_successor();
    let terminal_break = first_edge.filter(|&edge| {
        ir[edge].edge_type == EdgeType::Break && ir[edge].closure == Some(loop_stat)
    });
    let breaks: Vec<_> = ir[loop_stat]
        .label_edges
        .iter()
        .copied()
        .filter(|&edge| ir[edge].edge_type == EdgeType::Break && Some(edge) != terminal_break)
        .collect();
    if !breaks.is_empty()
        && (first_edge.is_some() && terminal_break.is_none()
            || !lift_breaks(ir, loop_stat, body, &breaks))
    {
        return false;
    }

    // Lifted break closures stay in place even if a continue prevents elimination.
    if find_edges_leaving(ir, body, loop_stat, false)
        .into_iter()
        .any(|edge| ir[edge].edge_type == EdgeType::Continue && ir[edge].destination == parent_loop)
    {
        return false;
    }

    remove_loop(ir, loop_stat, parent_loop, body);
    true
}

fn lift_breaks(ir: &mut Ir, loop_stat: StatId, body: StatId, breaks: &[EdgeId]) -> bool {
    let mut closures: Vec<_> = breaks
        .iter()
        .map(|&edge| min_break_closure(ir, body, ir[edge].source))
        .collect();
    let (existing_labels, labeled) = break_labels(ir, breaks, &closures);
    let before = existing_labels + usize::from(loop_stat.is_labeled(ir));

    for (&edge, closure) in breaks.iter().zip(&mut closures) {
        *closure = max_break_closure(ir, *closure, edge, &labeled, loop_stat);
    }

    let (_, labeled) = break_labels(ir, breaks, &closures);
    let after = labeled.values().filter(|&&labeled| labeled).count();
    if before <= after {
        return false;
    }

    for (&edge, &closure) in breaks.iter().zip(&closures) {
        closure.add_labeled_edge(ir, edge);
    }
    true
}

/// Record the current label count and the labels required by the proposed breaks.
fn break_labels(
    ir: &Ir,
    breaks: &[EdgeId],
    closures: &[StatId],
) -> (usize, FxHashMap<StatId, bool>) {
    let mut labels = FxHashMap::default();
    let mut existing = 0;
    for (&edge, &closure) in breaks.iter().zip(closures) {
        let labeled = labels.entry(closure).or_insert_with(|| {
            let labeled = closure.is_labeled(ir);
            existing += usize::from(labeled);
            labeled
        });
        *labeled |= is_break_labeled(ir, ir[edge].source, closure);
    }
    (existing, labels)
}

fn max_break_closure(
    ir: &Ir,
    minimum: StatId,
    edge: EdgeId,
    labeled: &FxHashMap<StatId, bool>,
    loop_stat: StatId,
) -> StatId {
    let mut highest = minimum;
    for closure in std::iter::successors(ir[minimum].parent, |&stat| ir[stat].parent) {
        if closure == loop_stat || closure.contains_statement_strict(ir, ir[edge].destination) {
            break;
        }
        let edge_labeled = is_break_labeled(ir, ir[edge].source, closure);
        let closure_labeled = labeled
            .get(&closure)
            .copied()
            .unwrap_or_else(|| closure.is_labeled(ir));
        if closure_labeled || !edge_labeled {
            highest = closure;
        }
    }
    highest
}

/// LowBreakHelper.getMinClosure descends only into a body that can finish the break.
fn min_break_closure(ir: &Ir, mut closure: StatId, source: StatId) -> StatId {
    loop {
        let can_lower = |&candidate: &StatId| {
            candidate.contains_statement_strict(ir, source)
                && ir[candidate].first_successor().is_none_or(|edge| {
                    ir[edge].closure == Some(closure) && ir[edge].edge_type == EdgeType::Break
                })
        };
        let next = match &ir[closure].kind {
            StatementKind::Sequence => ir[closure].stats.last().copied().filter(can_lower),
            StatementKind::If(branch) => branch
                .if_stat
                .filter(can_lower)
                .or_else(|| branch.else_stat.filter(can_lower)),
            StatementKind::Catch { .. } => ir[closure].stats.iter().copied().find(can_lower),
            StatementKind::Synchronized { body, .. } => Some(*body).filter(can_lower),
            _ => None,
        };
        let Some(next) = next else { return closure };
        closure = next;
    }
}

fn is_break_labeled(ir: &Ir, mut source: StatId, closure: StatId) -> bool {
    if !matches!(
        ir[closure].kind,
        StatementKind::Do(_) | StatementKind::Switch(_)
    ) {
        return true;
    }

    let mut labeled = false;
    loop {
        source = ir[source]
            .parent
            .expect("Break source is outside its closure");
        if source == closure {
            return labeled;
        }
        labeled |= matches!(
            ir[source].kind,
            StatementKind::Do(_) | StatementKind::Switch(_)
        );
    }
}

/// TryWithResourcesProcessor.findEdgesLeaving ignores an implicit edge when an
/// ancestor or the same source has already contributed an edge to its destination.
pub(super) fn find_edges_leaving(
    ir: &Ir,
    stat: StatId,
    region: StatId,
    allow_exit: bool,
) -> FxHashSet<EdgeId> {
    let mut edges = FxHashSet::default();
    collect_edges_leaving(
        ir,
        stat,
        region,
        allow_exit,
        &mut FxHashSet::default(),
        &mut edges,
    );
    edges
}

fn collect_edges_leaving(
    ir: &Ir,
    stat: StatId,
    region: StatId,
    allow_exit: bool,
    destinations: &mut FxHashSet<StatId>,
    edges: &mut FxHashSet<EdgeId>,
) {
    let mut added = Vec::new();
    for &edge in ir[stat].all_successors() {
        let target = ir[edge].destination;
        if target == region
            || region.contains_statement_strict(ir, target)
            || !allow_exit && matches!(ir[target].kind, StatementKind::DummyExit)
            || !ir[edge].explicit && destinations.contains(&target)
        {
            continue;
        }
        edges.insert(edge);
        if destinations.insert(target) {
            added.push(target);
        }
    }

    for &child in &ir[stat].stats {
        collect_edges_leaving(ir, child, region, allow_exit, destinations, edges);
    }
    for target in added {
        destinations.remove(&target);
    }
}

fn remove_loop(ir: &mut Ir, loop_stat: StatId, parent_loop: StatId, body: StatId) {
    if let Some(&edge) = body.get_successor_edges(ir, EdgeType::Break.mask()).first() {
        // The if-merging pass still needs a break that connects two if statements.
        if matches!(ir[ir[edge].destination].kind, StatementKind::If(_)) {
            edge.change_closure(ir, Some(parent_loop));
        } else {
            edge.remove(ir);
        }
    }

    let edges: Vec<_> = ir[loop_stat].label_edges.iter().copied().collect();
    for edge in edges {
        edge.change_destination(ir, parent_loop);
        parent_loop.add_labeled_edge(ir, edge);
    }
    loop_stat.replace_with(ir, body);
}
