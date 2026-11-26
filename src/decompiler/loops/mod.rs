// Copyright 2000-2020 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Loop recognition and rewrites in the Java method processor.

mod counted;
pub(crate) mod eliminate;
pub(crate) mod enhance;
pub(crate) mod extract;
mod foreach;
pub(crate) mod late;

use std::collections::VecDeque;

use rustc_hash::FxHashSet;

use super::exps::Expr;
use super::flow::{DirectEdgeType, DirectGraph, flatten::build_direct_graph};
use super::ir::{ExprId, ExprKind, ExprListId, Ir, StatId};
use super::stats::{StatementKind, stat_edge::EdgeType};
use crate::engine::method_timeout::checkpoint;
use crate::engine::{Cx, counter_container::CounterContainer};
use crate::structs::StructClass;

#[derive(Clone, Copy, PartialEq, Eq)]
enum LoopStyle {
    Java,
    Kotlin,
}

/// Native merge loop in MethodProcessor. Extraction restarts at elimination;
/// enhancement alone lets the remaining passes see the new loop immediately.
pub(crate) fn merge(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    root: StatId,
    class: &StructClass,
) -> std::io::Result<()> {
    let cx = &mut *cx.enter_method(counters);
    loop {
        checkpoint();
        if eliminate::eliminate(cx, counters, root, class)? {
            continue;
        }
        enhance::enhance(cx, counters, root)?;
        if extract::extract(cx, counters, root) {
            continue;
        }
        if !super::decompose::if_helper::merge_all_ifs(cx, counters, root, class) {
            return Ok(());
        }
    }
}

/// The last data statement in the region. An empty child can be skipped;
/// a child without a data exit stops the backwards search.
fn last_direct_data(ir: &Ir, stat: StatId) -> Option<StatId> {
    if ir[stat].exprents.is_some() {
        return Some(stat);
    }
    for &child in ir[stat].stats.iter().rev() {
        let data = last_direct_data(ir, child)?;
        if !ir[ir[data].exprents.unwrap()].is_empty() {
            return Some(data);
        }
    }
    None
}

/// Ascend through leading sequence members to find the regular predecessor
/// that can supply the loop initializer.
fn preceding_data(ir: &Ir, mut stat: StatId, require_basic: bool) -> Option<StatId> {
    while let Some(parent) = ir[stat].parent {
        if !matches!(ir[parent].kind, StatementKind::Sequence) {
            break;
        }
        if ir[parent].first != Some(stat) {
            let incoming = stat.get_predecessor_edges(ir, EdgeType::Regular.mask());
            let predecessor = ir[incoming[0]].source;
            if require_basic && !matches!(ir[predecessor].kind, StatementKind::BasicBlock { .. }) {
                return None;
            }
            return last_direct_data(ir, predecessor);
        }
        stat = parent;
    }
    None
}

/// MergeHelper scans predecessors for a local slot, irrespective of its SSA version.
fn is_var_used_before(ir: &mut Ir, root: StatId, stat: StatId, var: ExprId) -> bool {
    let ExprKind::Variable(var) = &ir[var].kind else {
        unreachable!("Loop use query requires a variable")
    };
    let index = var.index;
    let graph = build_direct_graph(ir, root);
    used_before(ir, &graph, stat, index)
}

fn used_before(ir: &Ir, graph: &DirectGraph, stat: StatId, index: i32) -> bool {
    let entry = graph.direct_node(stat).expect("Loop has no direct node");
    let incoming = graph[entry].predecessors(DirectEdgeType::Regular);
    let mut pending: VecDeque<_> = incoming.iter().copied().collect();
    let mut visited = FxHashSet::default();

    while let Some(node) = pending.pop_front() {
        let node = &graph[node];
        if node.stat == stat || stat.contains_statement_strict(ir, node.stat) {
            continue;
        }
        if ir[node.exprents]
            .iter()
            .any(|&expr| Expr::contains_var_index(ir, expr, index))
        {
            return true;
        }
        for &predecessor in node.predecessors(DirectEdgeType::Regular) {
            if visited.insert(predecessor) {
                pending.push_front(predecessor);
            }
        }
    }
    false
}

/// ArrayList.remove(Object) removes the first structurally equal expression.
fn remove_expr(cx: &mut Cx, list: ExprListId, expr: ExprId) {
    if let Some(index) = cx.ir[list]
        .iter()
        .position(|&other| Expr::equals(cx, expr, other))
    {
        cx.ir[list].remove(index);
    }
}

fn inherit_offsets(ir: &mut Ir, expr: ExprId, previous: ExprId) {
    let offsets = ir[previous].bytecode.clone();
    Expr::add_offsets(ir, expr, offsets.as_ref());
}
