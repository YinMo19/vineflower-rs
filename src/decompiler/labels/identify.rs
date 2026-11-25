// Copyright 2000-2020 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Identify explicit jumps and the jumps that need labels.

use indexmap::IndexMap;
use rustc_hash::{FxBuildHasher, FxHashSet};

use super::is_direct_path;
use crate::decompiler::exps::{ExprKind, FunctionType};
use crate::decompiler::ir::{EdgeId, Ir, StatId};
use crate::decompiler::stats::stat_edge::{EdgeType, StatEdge};
use crate::decompiler::stats::{LoopType, STATEDGE_ALL, StatementKind, SwitchStatement};

// Upstream hashes statements by JVM identity. A tie between equally large
// outgoing groups uses the first group in that hash table. Use the first
// group discovered by the traversal when there is no JVM identity order.
type OutgoingEdges = IndexMap<StatId, Vec<EdgeId>, FxBuildHasher>;

pub(crate) fn identify_labels(ir: &mut Ir, root: StatId) {
    set_explicit_edges(ir, root);
    process_statement_label(ir, root);
    set_ret_edges_unlabeled(ir, root);
    lift_sequence_label(ir, root);
}

fn set_explicit_edges(ir: &mut Ir, stat: StatId) -> OutgoingEdges {
    let mut outgoing = OutgoingEdges::default();
    if ir[stat].exprents.is_some() {
        return outgoing;
    }

    match ir[stat].kind {
        StatementKind::Catch { .. } | StatementKind::CatchAll { .. } => {
            let merge_handlers = matches!(ir[stat].kind, StatementKind::Catch { .. });
            for index in 0..ir[stat].stats.len() {
                let child = ir[stat].stats[index];
                let mut edges = set_explicit_edges(ir, child);
                process_edges_with_next(ir, child, &mut edges, None);

                // Edges leaving the finally handler stay explicit.
                if merge_handlers || Some(child) == ir[stat].first {
                    merge_edges(&mut outgoing, edges);
                }
            }
        }
        StatementKind::Do(_) => {
            let body = ir[stat].first.expect("Loop has no body");
            outgoing = set_explicit_edges(ir, body);
            process_edges_with_next(ir, body, &mut outgoing, Some(stat));
        }
        StatementKind::If(branch) => {
            if let Some(then_branch) = branch.if_stat {
                outgoing = set_explicit_edges(ir, then_branch);
                process_edges_with_next(ir, then_branch, &mut outgoing, None);

                if let Some(else_branch) = branch.else_stat {
                    let mut edges = set_explicit_edges(ir, else_branch);
                    process_edges_with_next(ir, else_branch, &mut edges, None);
                    merge_edges(&mut outgoing, edges);
                }
            } else {
                let head = ir[stat].first.expect("If statement has no head");
                process_edges_with_next(ir, head, &mut outgoing, None);
            }
        }
        StatementKind::Root { dummy_exit, .. } => {
            let body = ir[stat].first.expect("Root has no body");
            outgoing = set_explicit_edges(ir, body);
            process_edges_with_next(ir, body, &mut outgoing, Some(dummy_exit));
        }
        StatementKind::Sequence => {
            let count = ir[stat].stats.len();
            for index in 1..count {
                let child = ir[stat].stats[index - 1];
                let next = ir[stat].stats[index];
                let mut edges = set_explicit_edges(ir, child);
                process_edges_with_next(ir, child, &mut edges, Some(next));
            }
            let last = *ir[stat].stats.last().expect("Empty sequence");
            outgoing = set_explicit_edges(ir, last);
            process_edges_with_next(ir, last, &mut outgoing, None);
        }
        StatementKind::Switch(ref switch) => {
            let pattern = is_pattern_switch(ir, switch);
            let cases: Vec<_> = switch.cases.iter().map(|case| case.statement).collect();
            for adjacent in cases.windows(2) {
                let (case, next) = (adjacent[0], adjacent[1]);
                let next = if pattern {
                    next
                } else {
                    empty_block_successor(ir, next).map_or(next, |edge| ir[edge].destination)
                };
                let mut edges = set_explicit_edges(ir, case);
                process_edges_with_next(ir, case, &mut edges, Some(next));
            }
            if let Some(&last) = cases.last() {
                if let Some(edge) = empty_block_successor(ir, last) {
                    outgoing.insert(ir[edge].destination, vec![edge]);
                } else {
                    outgoing = set_explicit_edges(ir, last);
                    process_edges_with_next(ir, last, &mut outgoing, None);
                }
            }
        }
        StatementKind::Synchronized { body, .. } => {
            let head = ir[stat].first.expect("Synchronized statement has no head");
            let mut edges = set_explicit_edges(ir, head);
            process_edges_with_next(ir, head, &mut edges, Some(body));
            outgoing = set_explicit_edges(ir, body);
            process_edges_with_next(ir, body, &mut outgoing, None);
        }
        _ => {}
    }
    outgoing
}

fn merge_edges(outgoing: &mut OutgoingEdges, edges: OutgoingEdges) {
    for (target, edges) in edges {
        outgoing.entry(target).or_default().extend(edges);
    }
}

fn empty_block_successor(ir: &Ir, stat: StatId) -> Option<EdgeId> {
    ir[stat]
        .first_successor()
        .filter(|_| ir[stat].exprents.is_some_and(|list| ir[list].is_empty()))
}

fn is_pattern_switch(ir: &Ir, switch: &SwitchStatement) -> bool {
    !switch.case_guards.is_empty()
        || switch
            .cases
            .iter()
            .flat_map(|case| case.values.iter().flatten())
            .any(|&expr| {
                matches!(
                    ir[expr].kind,
                    ExprKind::Function {
                        op: FunctionType::InstanceOf,
                        ..
                    }
                )
            })
}

fn process_edges_with_next(
    ir: &mut Ir,
    stat: StatId,
    outgoing: &mut OutgoingEdges,
    mut next: Option<StatId>,
) {
    let successor = ir[stat].first_successor().filter(|&edge| {
        let destination = Some(ir[edge].destination);
        if destination == next {
            ir[edge].explicit = false;
            false
        } else {
            next = destination;
            true
        }
    });

    let is_loop = matches!(ir[stat].kind, StatementKind::Do(_));
    if matches!(ir[stat].kind, StatementKind::Do(loop_stat) if loop_stat.ty == LoopType::Infinite) {
        next = None;
    }

    if ir[stat].phantom && matches!(ir[stat].kind, StatementKind::Switch(_)) {
        // Implicit, unlabeled yield edges survive exit condensation.
        for &edge in &ir.stats[stat].label_edges {
            ir.edges[edge].explicit = false;
            ir.edges[edge].labeled = false;
        }
    }

    if let Some(next) = next {
        if let Some(edges) = outgoing.get(&next) {
            let is_if = matches!(ir[stat].kind, StatementKind::If(_));
            for &edge in edges {
                let closure = ir[edge].closure;
                if is_loop && closure == Some(stat)
                    || is_if
                        && closure.is_some_and(|stat| matches!(ir[stat].kind, StatementKind::Do(_)))
                        && matches!(
                            ir[ir[edge].destination].kind,
                            StatementKind::DummyExit { .. }
                        )
                {
                    continue;
                }
                ir[edge].explicit = false;
            }
        } else if ir[stat].first_successor().is_none()
            && let Some(edges) = largest_outgoing_group(ir, outgoing)
            && edges.len() > 1
        {
            add_common_successor(ir, stat, edges);
        }
        outgoing.clear();
    } else if outgoing.len() == 1
        && let Some((&target, edges)) = outgoing.first()
        && edges.len() > 1
        && !matches!(ir[target].kind, StatementKind::DummyExit { .. })
    {
        let edge = add_common_successor(ir, stat, edges);
        outgoing.insert(ir[edge].destination, vec![edge]);
    }

    if let Some(edge) = successor {
        outgoing.insert(ir[edge].destination, vec![edge]);
    }
}

fn largest_outgoing_group<'a>(ir: &Ir, outgoing: &'a OutgoingEdges) -> Option<&'a [EdgeId]> {
    let mut largest: Option<&[EdgeId]> = None;
    for (&target, edges) in outgoing {
        if !matches!(ir[target].kind, StatementKind::DummyExit { .. })
            && largest.is_none_or(|previous| edges.len() > previous.len())
        {
            largest = Some(edges);
        }
    }
    largest
}

fn add_common_successor(ir: &mut Ir, stat: StatId, edges: &[EdgeId]) -> EdgeId {
    let example = &ir[edges[0]];
    let parent = ir[stat].parent.expect("Merged successors require a parent");
    let closure = match example.closure {
        Some(closure) if parent.contains_statement_strict(ir, closure) => Some(parent),
        closure => closure,
    };
    let edge = StatEdge::new(ir, example.edge_type, stat, example.destination, closure);
    stat.add_successor(ir, edge);
    for &edge in edges {
        ir[edge].explicit = false;
    }
    edge
}

#[derive(Default)]
struct LabelSets {
    breaks: FxHashSet<StatId>,
    continues: FxHashSet<StatId>,
}

fn process_statement_label(ir: &mut Ir, stat: StatId) -> LabelSets {
    let mut sets = LabelSets::default();
    if ir[stat].exprents.is_none() {
        for index in 0..ir[stat].stats.len() {
            let child = process_statement_label(ir, ir[stat].stats[index]);
            sets.breaks.extend(child.breaks);
            sets.continues.extend(child.continues);
        }

        let is_loop = matches!(ir[stat].kind, StatementKind::Do(_));
        if is_loop || matches!(ir[stat].kind, StatementKind::Switch(_)) {
            for &edge in &ir.stats[stat].label_edges {
                let edge = &mut ir.edges[edge];
                if edge.explicit
                    && match edge.edge_type {
                        EdgeType::Break => sets.breaks.contains(&edge.source),
                        EdgeType::Continue => sets.continues.contains(&edge.source),
                        _ => false,
                    }
                {
                    edge.labeled = false;
                }
            }
            sets.breaks.clear();
            if is_loop {
                sets.continues.clear();
            }
        }
    }

    sets.breaks.insert(stat);
    sets.continues.insert(stat);
    sets
}

fn set_ret_edges_unlabeled(ir: &mut Ir, root: StatId) {
    let StatementKind::Root { dummy_exit, .. } = ir[root].kind else {
        unreachable!("Expected a root statement");
    };
    for edge in dummy_exit.get_predecessor_edges(ir, STATEDGE_ALL) {
        let source = ir[edge].source;
        let exits = ir[source]
            .exprents
            .and_then(|list| ir[list].last())
            .is_some_and(|&last| matches!(ir[last].kind, ExprKind::Exit { .. }));
        if ir[edge].edge_type == EdgeType::FinallyExit || exits {
            ir[edge].labeled = false;
        }
    }
}

fn lift_sequence_label(ir: &mut Ir, stat: StatId) {
    if matches!(ir[stat].kind, StatementKind::Sequence)
        && let Some(parent) = ir[stat].parent
        && matches!(ir[parent].kind, StatementKind::If(branch) if branch.if_stat == Some(stat))
        && ir[stat]
            .label_edges
            .iter()
            .all(|&edge| is_direct_path(ir, parent, ir[edge].destination))
    {
        // Java iterates an identity hash set of the moved labels.
        let labels: Vec<_> = ir[stat].label_edges.iter().copied().collect();
        for edge in labels {
            parent.add_labeled_edge(ir, edge);
        }
    }

    for index in 0..ir[stat].stats.len() {
        lift_sequence_label(ir, ir[stat].stats[index]);
    }
}
