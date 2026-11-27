//! Normalizes statement edges and their label closures.

pub(crate) mod finish;
mod identify;
pub(crate) use identify::identify_labels;

use indexmap::IndexSet;

use crate::decompiler::ir::{EdgeId, Ir, StatId};
use crate::decompiler::stats::stat_edge::EdgeType;
use crate::decompiler::stats::{LoopType, STATEDGE_ALL, StatementKind};

pub(crate) fn clean_up_edges(ir: &mut Ir, root: StatId) {
    reset_all_edges(ir, root);
    remove_non_immediate_edges(ir, root);
    lift_closures(ir, root);
    low_continue_labels(ir, root);
    low_closures(ir, root);
}

fn reset_all_edges(ir: &mut Ir, stat: StatId) {
    for index in 0..ir[stat].stats.len() {
        reset_all_edges(ir, ir[stat].stats[index]);
    }

    for edge in stat.get_successor_edges(ir, STATEDGE_ALL) {
        ir[edge].explicit = true;
        ir[edge].labeled = true;
    }
}

fn remove_non_immediate_edges(ir: &mut Ir, stat: StatId) {
    for index in 0..ir[stat].stats.len() {
        remove_non_immediate_edges(ir, ir[stat].stats[index]);
    }

    if !ir[stat].has_basic_succ_edge() {
        let mask = EdgeType::Continue.mask() | EdgeType::Break.mask();
        for edge in stat.get_successor_edges(ir, mask) {
            stat.remove_successor(ir, edge);
        }
    }
}

fn lift_closures(ir: &mut Ir, stat: StatId) {
    for edge in stat.get_successor_edges(ir, STATEDGE_ALL) {
        let destination = ir[edge].destination;
        match ir[edge].edge_type {
            EdgeType::Continue if ir[edge].closure != Some(destination) => {
                destination.add_labeled_edge(ir, edge);
            }
            EdgeType::Break => lift_break_closure(ir, edge, destination),
            _ => {}
        }
    }

    for index in 0..ir[stat].stats.len() {
        lift_closures(ir, ir[stat].stats[index]);
    }
}

fn lift_break_closure(ir: &mut Ir, edge: EdgeId, destination: StatId) {
    if matches!(ir[destination].kind, StatementKind::DummyExit { .. }) {
        return;
    }
    let Some(parent) = ir[destination].parent else {
        return;
    };

    let preceding_closure = |previous: StatId, next: StatId| {
        (next == destination && !matches!(ir[previous].kind, StatementKind::BasicBlock { .. }))
            .then_some(previous)
    };
    let closure = match &ir[parent].kind {
        StatementKind::Sequence => ir[parent]
            .stats
            .windows(2)
            .find_map(|pair| preceding_closure(pair[0], pair[1])),
        StatementKind::Switch(switch) => switch
            .cases
            .windows(2)
            .find_map(|pair| preceding_closure(pair[0].statement, pair[1].statement)),
        _ => None,
    };
    if let Some(closure) = closure {
        closure.add_labeled_edge(ir, edge);
    }
}

pub(crate) fn low_continue_labels(ir: &mut Ir, root: StatId) {
    lower_continue_labels(ir, root, &mut IndexSet::new());
}

fn lower_continue_labels(ir: &mut Ir, stat: StatId, edges: &mut IndexSet<EdgeId>) {
    let lower = match ir[stat].kind {
        StatementKind::Do(loop_stat) => match loop_stat.ty {
            LoopType::Infinite => true,
            LoopType::While => loop_stat.condition(ir).is_none(),
            LoopType::For => loop_stat.increment(ir).is_none(),
            LoopType::DoWhile | LoopType::ForEach => false,
        },
        _ => true,
    };
    if lower {
        edges.extend(stat.get_predecessor_edges(ir, EdgeType::Continue.mask()));
    }
    if lower && matches!(ir[stat].kind, StatementKind::Do(_)) {
        for &edge in edges.iter() {
            if stat.contains_statement_strict(ir, ir[edge].source) {
                edge.change_destination(ir, stat);
                stat.add_labeled_edge(ir, edge);
            }
        }
    }

    for index in 0..ir[stat].stats.len() {
        let child = ir[stat].stats[index];
        if Some(child) == ir[stat].first {
            lower_continue_labels(ir, child, edges);
        } else {
            lower_continue_labels(ir, child, &mut IndexSet::new());
        }
    }
}

pub(crate) fn low_closures(ir: &mut Ir, stat: StatId) {
    let labels: Vec<_> = ir[stat].label_edges.iter().copied().collect();
    for edge in labels {
        if ir[edge].edge_type != EdgeType::Break {
            continue;
        }
        let source = ir[edge].source;
        let destination = ir[edge].destination;
        for index in 0..ir[stat].stats.len() {
            let child = ir[stat].stats[index];
            if child.contains_statement_strict(ir, source) && is_direct_path(ir, child, destination)
            {
                child.add_labeled_edge(ir, edge);
            }
        }
    }

    for index in 0..ir[stat].stats.len() {
        low_closures(ir, ir[stat].stats[index]);
    }
}

/// The destination reached after a statement finishes, as in MergeHelper.isDirectPath.
pub(crate) fn is_direct_path(ir: &Ir, mut stat: StatId, end: StatId) -> bool {
    loop {
        let edges = ir[stat].direct_successors();
        if !edges.is_empty() {
            return edges.iter().any(|&edge| ir[edge].destination == end);
        }

        let Some(parent) = ir[stat].parent else {
            return matches!(ir[end].kind, StatementKind::DummyExit { .. });
        };
        match &ir[parent].kind {
            StatementKind::Root { .. } => {
                return matches!(ir[end].kind, StatementKind::DummyExit { .. });
            }
            StatementKind::Do(_) => return end == parent,
            StatementKind::Switch(switch) => {
                for cases in switch.cases.windows(2) {
                    if cases[0].statement == stat {
                        let mut next = cases[1].statement;
                        if ir[next].exprents.is_some_and(|list| ir[list].is_empty()) {
                            let edge = ir[next].first_successor().unwrap_or_else(|| {
                                panic!("Statement {} has no successors", ir[next].id)
                            });
                            next = ir[edge].destination;
                        }
                        return end == next;
                    }
                }
            }
            _ => {}
        }
        stat = parent;
    }
}
