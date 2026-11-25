// Copyright 2000-2020 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! The statement rewrites at the end of `DomHelper.parseGraph`.

use indexmap::IndexSet;
use rustc_hash::FxHashSet;

use crate::code::code_constants::OPC_MONITOREXIT;
use crate::decompiler::ir::{EdgeId, ExprListId, Ir, StatId};
use crate::decompiler::stats::stat_edge::{EdgeType, StatEdge};
use crate::decompiler::stats::{STATEDGE_ALL, STATEDGE_DIRECT_ALL, Statement, StatementKind};
use crate::engine::counter_container::{CounterContainer, EXPRESSION_COUNTER};

pub fn finish(ir: &mut Ir, counters: &mut CounterContainer, root: StatId) {
    low_continue_labels(ir, root, &mut IndexSet::new());
    condense_sequences(ir, counters, root);
    root.build_monitor_flags(ir);
    build_synchronized(ir, counters, root);
}

fn low_continue_labels(ir: &mut Ir, stat: StatId, edges: &mut IndexSet<EdgeId>) {
    edges.extend(stat.get_predecessor_edges(ir, EdgeType::Continue.mask()));
    // At this stage all Do statements still have the initial infinite loop type.
    if matches!(ir[stat].kind, StatementKind::Do) {
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
            low_continue_labels(ir, child, edges);
        } else {
            low_continue_labels(ir, child, &mut IndexSet::new());
        }
    }
}

fn condense_sequences(ir: &mut Ir, counters: &mut CounterContainer, mut stat: StatId) {
    if matches!(ir[stat].kind, StatementKind::Sequence) {
        let mut children = ir[stat].stats.to_vec();
        let mut index = 0;
        let mut unfolded = false;
        while let Some(&child) = children.get(index) {
            if matches!(ir[child].kind, StatementKind::Sequence) {
                remove_empty_statements(ir, child);
                let next = children.get(index + 1).copied();
                if next.is_none_or(|next| is_sequence_disbandable(ir, child, next)) {
                    unfold_sequence(ir, stat, child, next);
                    children.splice(index..=index, ir[child].stats.iter().copied());
                    unfolded = true;
                    continue;
                }
            }
            index += 1;
        }
        if unfolded {
            let sequence = Statement::new_sequence(ir, counters, &children);
            sequence.set_all_parent(ir);
            let parent = ir[stat].parent.expect("Sequence has no parent");
            parent.replace_statement(ir, stat, sequence);
            stat = sequence;
        }

        remove_empty_statements(ir, stat);
        if ir[stat].stats.len() == 1 {
            let child = ir[stat].first.unwrap();
            let child_edge = first_successor(ir, child);
            let parent_edge = first_successor(ir, stat);
            let can_disband = match (child_edge, parent_edge) {
                (Some(edge), Some(outer)) => {
                    if ir[edge].destination == ir[outer].destination {
                        edge.remove(ir);
                        true
                    } else {
                        false
                    }
                }
                _ => true,
            };
            if can_disband {
                let parent = ir[stat].parent.expect("Sequence has no parent");
                parent.replace_statement(ir, stat, child);
                stat = child;
            }
        }
    }

    while let Some(child) = ir[stat].stats.iter().copied().find(|&child| {
        (ir[child].stats.is_empty() || ir[child].exprents.is_some())
            && !matches!(ir[child].kind, StatementKind::BasicBlock { .. })
    }) {
        destroy_and_flatten_statement(ir, counters, stat, child);
    }
    for index in 0..ir[stat].stats.len() {
        let child = ir[stat].stats[index];
        condense_sequences(ir, counters, child);
    }
}

fn first_successor(ir: &Ir, stat: StatId) -> Option<EdgeId> {
    stat.get_successor_edges(ir, STATEDGE_ALL).first().copied()
}

fn is_sequence_disbandable(ir: &Ir, stat: StatId, next: StatId) -> bool {
    let last = *ir[stat].stats.get_last();
    first_successor(ir, last).is_none_or(|edge| ir[edge].destination == next)
        && next
            .get_predecessor_edges(ir, EdgeType::Break.mask())
            .into_iter()
            .all(|edge| {
                let source = ir[edge].source;
                source == last || last.contains_statement_strict(ir, source)
            })
}

fn unfold_sequence(ir: &mut Ir, parent: StatId, stat: StatId, next: Option<StatId>) {
    let first = ir[stat].first.unwrap();
    for edge in stat.get_predecessor_edges(ir, STATEDGE_ALL) {
        edge.change_destination(ir, first);
    }

    let last = *ir[stat].stats.get_last();
    let successors = last.get_successor_edges(ir, STATEDGE_ALL);
    if successors.is_empty()
        && let Some(next) = next
    {
        let edge = StatEdge::new(ir, EdgeType::Regular, last, next, None);
        last.add_successor(ir, edge);
    } else {
        for edge in successors {
            if next.is_some() {
                edge.change_type(ir, EdgeType::Regular);
                assert!(ir[edge].closure.is_some(), "Sequence exit has no closure");
                edge.change_closure(ir, None);
            } else if ir[edge].closure == Some(stat) {
                parent.add_labeled_edge(ir, edge);
            }
        }
    }

    for edge in stat.get_successor_edges(ir, STATEDGE_ALL) {
        edge.remove(ir);
    }
    let label_owner = if matches!(ir[last].kind, StatementKind::BasicBlock { .. }) {
        parent
    } else {
        last
    };
    let labels: Vec<_> = ir[stat].label_edges.iter().copied().collect();
    for edge in labels {
        if ir[edge].source != last {
            label_owner.add_labeled_edge(ir, edge);
        }
    }
    clear_closure(ir, stat, stat);
}

fn clear_closure(ir: &mut Ir, stat: StatId, closure: StatId) {
    for edge in stat.get_successor_edges(ir, STATEDGE_ALL) {
        if ir[edge].closure == Some(closure) {
            edge.change_closure(ir, None);
        }
    }
    for index in 0..ir[stat].stats.len() {
        let child = ir[stat].stats[index];
        clear_closure(ir, child, closure);
    }
}

fn remove_empty_statements(ir: &mut Ir, sequence: StatId) {
    if ir[sequence].stats.len() <= 1 {
        return;
    }
    merge_flat_statements(ir, sequence);

    let mut index = 0;
    while let Some(&stat) = ir[sequence].stats.get(index) {
        if ir[stat].exprents.is_some_and(|list| ir[list].is_empty())
            && remove_empty_statement(ir, stat)
        {
            let key = ir[stat].id;
            ir[sequence].stats.remove_with_key(&key);
            index = 0;
        } else {
            index += 1;
        }
    }
    if let Some(&first) = ir[sequence].stats.first() {
        ir[sequence].first = Some(first);
    }
}

fn remove_empty_statement(ir: &mut Ir, stat: StatId) -> bool {
    let Some(outgoing) = first_successor(ir, stat) else {
        if !stat
            .get_predecessor_edges(ir, EdgeType::Break.mask())
            .is_empty()
        {
            return false;
        }
        for edge in stat.get_predecessor_edges(ir, STATEDGE_ALL) {
            edge.remove(ir);
        }
        return true;
    };
    let (kind, destination, closure) = (
        ir[outgoing].edge_type,
        ir[outgoing].destination,
        ir[outgoing].closure,
    );
    if kind == EdgeType::FinallyExit {
        return false;
    }
    outgoing.remove(ir);
    for edge in stat.get_predecessor_edges(ir, STATEDGE_ALL) {
        if kind != EdgeType::Regular {
            edge.change_type(ir, kind);
        }
        edge.change_destination(ir, destination);
        if let Some(closure) = closure {
            closure.add_labeled_edge(ir, edge);
        }
    }
    // This retired statement's label set is left in place by SequenceHelper.
    let labels: Vec<_> = ir[stat].label_edges.iter().copied().collect();
    for edge in labels {
        if ir[edge].closure == Some(stat) {
            ir[edge].closure = None;
        }
    }
    true
}

fn merge_flat_statements(ir: &mut Ir, sequence: StatId) {
    loop {
        let mut merged = false;
        for index in (1..ir[sequence].stats.len()).rev() {
            let current = ir[sequence].stats[index - 1];
            let next = ir[sequence].stats[index];
            if let Some(list) = ir[current].exprents.filter(|&list| !ir[list].is_empty())
                && let Some(destination) = first_expression_list(ir, next)
            {
                let expressions = std::mem::take(&mut ir[list]);
                if list != destination {
                    ir[destination].splice(0..0, expressions);
                }
                merged = true;
            }
        }
        if !merged {
            break;
        }
    }
}

fn first_expression_list(ir: &Ir, mut stat: StatId) -> Option<ExprListId> {
    loop {
        if let Some(list) = ir[stat].exprents {
            return Some(list);
        }
        match ir[stat].kind {
            StatementKind::If(_)
            | StatementKind::Sequence
            | StatementKind::Switch(_)
            | StatementKind::Synchronized { .. } => stat = ir[stat].first.unwrap(),
            _ => return None,
        }
    }
}

fn destroy_and_flatten_statement(
    ir: &mut Ir,
    counters: &mut CounterContainer,
    parent: StatId,
    stat: StatId,
) {
    destroy_statement_content(ir, stat, false);
    let replacement = Statement::new_empty_basic_block(ir, counters);
    let expressions = ir[replacement].exprents.unwrap();
    if let Some(list) = ir[stat].exprents {
        for index in 0..ir[list].len() {
            let mut expression = ir[ir[list][index]].clone();
            expression.id = counters.get_counter_and_increment(EXPRESSION_COUNTER);
            let copied = ir.exprs.push(expression);
            ir[expressions].push(copied);
        }
    }
    parent.replace_statement(ir, stat, replacement);
}

fn destroy_statement_content(ir: &mut Ir, stat: StatId, remove_self: bool) {
    for index in 0..ir[stat].stats.len() {
        let child = ir[stat].stats[index];
        destroy_statement_content(ir, child, true);
    }
    ir[stat].stats.clear();
    if remove_self {
        for edge in stat.get_successor_edges(ir, STATEDGE_ALL) {
            edge.remove(ir);
        }
        for edge in stat.get_predecessor_edges(ir, STATEDGE_ALL) {
            edge.remove(ir);
        }
    }
}

/// Recognizes monitor-enter and cleanup pairs after the initial parse or a finally rewrite.
pub fn build_synchronized(ir: &mut Ir, counters: &mut CounterContainer, stat: StatId) -> bool {
    let mut changed = false;
    for index in 0..ir[stat].stats.len() {
        let child = ir[stat].stats[index];
        changed |= build_synchronized(ir, counters, child);
    }
    if matches!(ir[stat].kind, StatementKind::Sequence) {
        let mut index = 0;
        while index + 1 < ir[stat].stats.len() {
            let head = ir[stat].stats[index];
            let next = ir[stat].stats[index + 1];
            if ir[head].is_monitor_enter && build_monitor(ir, counters, stat, head, next) {
                changed = true;
                index = 0;
            } else {
                index += 1;
            }
        }
    }
    changed
}

fn build_monitor(
    ir: &mut Ir,
    counters: &mut CounterContainer,
    sequence: StatId,
    head: StatId,
    next: StatId,
) -> bool {
    let mut catch_all = next;
    while matches!(ir[catch_all].kind, StatementKind::Sequence) {
        catch_all = ir[catch_all].first.unwrap();
    }
    let StatementKind::CatchAll {
        handler,
        is_finally,
        ..
    } = ir[catch_all].kind
    else {
        return false;
    };
    let body = ir[catch_all].first.unwrap();
    let head_ok =
        ir[body].contains_monitor_exit_or_athrow() || has_no_exits(ir, body) || is_finally;
    if !head_ok {
        return false;
    }
    let handler = handler.expect("Catch-all statement has no handler");
    if !ir[handler].contains_monitor_exit {
        return false;
    }

    mark_monitorexit_dead(ir, body);
    mark_monitorexit_dead(ir, handler);
    let parent = ir[catch_all].parent.unwrap();
    for stat in [catch_all, parent] {
        for edge in stat.get_successor_edges(ir, EdgeType::Regular.mask()) {
            mark_monitorexit_dead(ir, ir[edge].destination);
        }
    }

    head.get_successor_edges(ir, STATEDGE_DIRECT_ALL)[0].remove(ir);
    for edge in head.get_predecessor_edges(ir, STATEDGE_DIRECT_ALL) {
        edge.change_destination(ir, next);
    }
    let head_id = ir[head].id;
    ir[sequence].stats.remove_with_key(&head_id);
    ir[sequence].first = Some(ir[sequence].stats[0]);

    let synchronized = Statement::new_synchronized(ir, counters, head, body, handler);
    synchronized.set_all_parent(ir);
    let labels: Vec<_> = ir[catch_all].label_edges.iter().copied().collect();
    for edge in labels {
        synchronized.add_labeled_edge(ir, edge);
    }
    let edge = StatEdge::new(ir, EdgeType::Regular, head, body, None);
    head.add_successor(ir, edge);
    parent.replace_statement(ir, catch_all, synchronized);
    true
}

fn mark_monitorexit_dead(ir: &mut Ir, stat: StatId) {
    if let StatementKind::BasicBlock { block } = ir[stat].kind {
        if ir[block]
            .seq
            .iter()
            .any(|instr| instr.opcode == OPC_MONITOREXIT)
        {
            ir[stat].removable_monitorexit = true;
        }
    } else {
        for index in 0..ir[stat].stats.len() {
            let child = ir[stat].stats[index];
            mark_monitorexit_dead(ir, child);
        }
    }
}

fn has_no_exits(ir: &Ir, head: StatId) -> bool {
    let mut nodes = vec![head];
    let mut index = 0;
    while let Some(&stat) = nodes.get(index) {
        nodes.extend_from_slice(&ir[stat].stats);
        index += 1;
    }
    let members: FxHashSet<_> = nodes.iter().copied().collect();
    nodes.iter().all(|&stat| {
        stat.get_successor_edges(ir, STATEDGE_DIRECT_ALL)
            .into_iter()
            .all(|edge| members.contains(&ir[edge].destination))
    })
}
