//! T1/T2 reduction and statement copying from IrreducibleCFGDeobfuscator.
use rustc_hash::{FxHashMap, FxHashSet};

use crate::decompiler::ir::{Ir, StatId};
use crate::decompiler::stats::recognize::{get_simple_copy, init_simple_copy};
use crate::decompiler::stats::stat_edge::{EdgeType, StatEdge};
use crate::decompiler::stats::{EdgeDirection, STATEDGE_DIRECT_ALL, StatementKind};
use crate::engine::counter_container::CounterContainer;
use crate::util::jhash::JHashMap;

#[derive(Default)]
struct Node {
    predecessors: FxHashSet<i32>,
    successors: FxHashSet<i32>,
}

pub(super) fn is_irreducible(ir: &Ir, general: StatId) -> bool {
    let mut nodes = JHashMap::new();
    for &stat in &ir[general].stats {
        if !stat
            .get_successor_edges(ir, EdgeType::Exception.mask())
            .is_empty()
        {
            return false;
        }
        nodes.insert(ir[stat].id, Node::default());
    }
    for &stat in &ir[general].stats {
        let id = ir[stat].id;
        for succ in stat.get_neighbours(ir, EdgeType::Regular.mask(), EdgeDirection::Forward) {
            let other = ir[succ].id;
            nodes.get_mut(&id).unwrap().successors.insert(other);
            nodes.get_mut(&other).unwrap().predecessors.insert(id);
        }
    }
    loop {
        let reducible = nodes
            .iter()
            .find(|(id, node)| node.successors.contains(id) || node.predecessors.len() == 1)
            .map(|(&id, _)| id);
        let Some(id) = reducible else {
            return nodes.len() > 1;
        };
        let node = nodes.get_mut(&id).unwrap();
        if node.successors.remove(&id) {
            node.predecessors.remove(&id);
        } else {
            let node = nodes.remove(&id).unwrap();
            let pred = *node.predecessors.iter().next().unwrap();
            let pred_succs = &mut nodes.get_mut(&pred).unwrap().successors;
            pred_succs.extend(&node.successors);
            pred_succs.remove(&id);
            for succ in node.successors {
                let incoming = &mut nodes.get_mut(&succ).unwrap().predecessors;
                incoming.remove(&id);
                incoming.insert(pred);
            }
        }
    }
}

fn statement_size(ir: &Ir, stat: StatId) -> i32 {
    match ir[stat].kind {
        StatementKind::BasicBlock { block } => ir[block].size(),
        _ => ir[stat].stats.iter().fold(0i32, |size, &child| {
            size.wrapping_add(statement_size(ir, child))
        }),
    }
}

pub(super) fn split(ir: &mut Ir, counters: &mut CounterContainer, general: StatId) -> bool {
    let candidate = ir[general]
        .stats
        .iter()
        .copied()
        .filter_map(|stat| {
            let degree = |direction| {
                stat.get_neighbours(ir, EdgeType::Regular.mask(), direction)
                    .into_iter()
                    .collect::<FxHashSet<_>>()
                    .len()
            };
            let preds = degree(EdgeDirection::Backward);
            (preds > 1).then(|| {
                (
                    (
                        degree(EdgeDirection::Forward),
                        statement_size(ir, stat).wrapping_mul((preds - 1) as i32),
                    ),
                    stat,
                )
            })
        })
        .min_by_key(|(cost, _)| *cost);
    let Some((_, stat)) = candidate else {
        return false;
    };
    let entry = stat.get_predecessor_edges(ir, EdgeType::Regular.mask())[0];
    let copy = get_simple_copy(ir, counters, stat);
    let mut copies = FxHashMap::default();
    copies.insert(stat, copy);
    copy_children(ir, counters, stat, copy, &mut copies);
    init_tree(ir, counters, copy);
    ir[copy].parent = Some(general);
    let id = ir[copy].id;
    ir[general].stats.add_with_key(copy, id);

    let source = ir[entry].source;
    for edge in stat.get_predecessor_edges(ir, STATEDGE_DIRECT_ALL) {
        if ir[edge].source == source || ir[edge].closure == Some(source) {
            edge.change_destination(ir, copy);
        }
    }
    for edge in stat.get_successor_edges(ir, STATEDGE_DIRECT_ALL) {
        let edge = StatEdge::new(
            ir,
            ir[edge].edge_type,
            copy,
            ir[edge].destination,
            ir[edge].closure,
        );
        copy.add_successor(ir, edge);
    }
    true
}

fn copy_children(
    ir: &mut Ir,
    counters: &mut CounterContainer,
    old: StatId,
    new: StatId,
    copies: &mut FxHashMap<StatId, StatId>,
) {
    // Upstream allocates sibling copies first, then copies their outgoing
    // edges before descending. References to nodes outside the map stay shared.
    let children = ir[old].stats.to_vec();
    for &child in &children {
        let copy = get_simple_copy(ir, counters, child);
        copies.insert(child, copy);
        let id = ir[copy].id;
        ir[new].stats.add_with_key(copy, id);
    }
    for &child in &children {
        let copy = copies[&child];
        for edge in child.get_successor_edges(ir, STATEDGE_DIRECT_ALL) {
            let dest = ir[edge].destination;
            let closure = ir[edge]
                .closure
                .map(|old| copies.get(&old).copied().unwrap_or(old));
            let edge = StatEdge::new(
                ir,
                ir[edge].edge_type,
                copy,
                copies.get(&dest).copied().unwrap_or(dest),
                closure,
            );
            copy.add_successor(ir, edge);
        }
    }
    for child in children {
        copy_children(ir, counters, child, copies[&child], copies);
    }
}

fn init_tree(ir: &mut Ir, counters: &mut CounterContainer, stat: StatId) {
    init_simple_copy(ir, counters, stat);
    ir[stat].copied = true;
    for index in 0..ir[stat].stats.len() {
        let child = ir[stat].stats[index];
        ir[child].parent = Some(stat);
        init_tree(ir, counters, child);
    }
}
