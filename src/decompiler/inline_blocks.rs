// Copyright 2000-2020 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Inline a sequence tail into the source of its single incoming break.

use std::io;

use crate::decompiler::decompose::finish::condense_sequences;
use crate::decompiler::ir::{Ir, StatId};
use crate::decompiler::labels::is_direct_path;
use crate::decompiler::stats::recognize::sort_switch_edges;
use crate::decompiler::stats::stat_edge::{EdgeType, StatEdge};
use crate::decompiler::stats::{IfStatement, Statement, StatementKind};
use crate::engine::{Cx, counter_container::CounterContainer};

pub(crate) fn inline(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    root: StatId,
) -> io::Result<bool> {
    let mut changed = false;
    while inline_rec(&mut cx.ir, counters, root)? {
        changed = true;
    }
    if changed {
        condense_sequences(cx, counters, root);
    }
    Ok(changed)
}

fn inline_rec(ir: &mut Ir, counters: &mut CounterContainer, stat: StatId) -> io::Result<bool> {
    let mut changed = false;
    for index in 0..ir[stat].stats.len() {
        changed |= inline_rec(ir, counters, ir[stat].stats[index])?;
    }

    if matches!(ir[stat].kind, StatementKind::Sequence) {
        for index in 1..ir[stat].stats.len() {
            if is_inlineable(ir, stat, index) {
                inline_block(ir, counters, stat, index)?;
                return Ok(true);
            }
        }
    }
    Ok(changed)
}

fn inline_block(
    ir: &mut Ir,
    counters: &mut CounterContainer,
    sequence: StatId,
    index: usize,
) -> io::Result<()> {
    let first = ir[sequence].stats[index];
    let preceding = ir[sequence].stats[index - 1];
    ir[preceding]
        .first_successor()
        .expect("Missing predecessor successor")
        .remove(ir);

    let edge = first
        .get_predecessor_edges(ir, EdgeType::Break.mask())
        .first()
        .copied()
        .ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                "Inlined block has no break predecessor",
            )
        })?;
    let source = ir[edge].source;
    let parent = ir[source].parent.expect("Inline source has no parent");
    edge.remove(ir);

    let mut children = Vec::with_capacity(ir[sequence].stats.len() - index + 1);
    for position in (index..ir[sequence].stats.len()).rev() {
        children.push(ir[sequence].stats.remove(position));
    }
    if matches!(
        ir[parent].kind,
        StatementKind::If(IfStatement {
            has_else: false,
            ..
        })
    ) && ir[parent].first == Some(source)
    {
        children.reverse();
        let body = Statement::new_sequence(ir, counters, &children);
        body.set_all_parent(ir);
        let edge = StatEdge::new(ir, EdgeType::Regular, source, body, None);
        source.add_successor(ir, edge);
        let StatementKind::If(branch) = &mut ir[parent].kind else {
            unreachable!();
        };
        branch.if_edge = Some(edge);
        branch.if_stat = Some(body);
        let id = ir[body].id;
        ir[parent].stats.add_with_key(body, id);
        ir[body].parent = Some(parent);
    } else {
        children.push(source);
        children.reverse();
        let block = Statement::new_sequence(ir, counters, &children);
        block.set_all_parent(ir);
        parent.replace_statement(ir, source, block);

        // These continues may point forward, so move them directly to the source.
        for edge in block.get_predecessor_edges(ir, EdgeType::Continue.mask()) {
            edge.change_destination(ir, source);
            source.add_labeled_edge(ir, edge);
        }
        if matches!(ir[parent].kind, StatementKind::Switch(_)) {
            sort_switch_edges(ir, counters, parent);
        }
        let edge = StatEdge::new(ir, EdgeType::Regular, source, first, None);
        source.add_successor(ir, edge);

        let last = *ir[block].stats.get_last();
        if ir[last].first_successor().is_none() {
            lift_terminal_breaks(ir, parent, last)?;
        }
    }
    Ok(())
}

fn lift_terminal_breaks(ir: &mut Ir, parent: StatId, last: StatId) -> io::Result<()> {
    let labels: Vec<_> = ir[last].label_edges.iter().copied().collect();
    for edge in labels {
        let destination = ir[edge].destination;
        if ir[edge].edge_type != EdgeType::Break || !is_direct_path(ir, last, destination) {
            continue;
        }
        let closure = std::iter::successors(Some(parent), |&stat| ir[stat].parent)
            .find(|&stat| is_direct_path(ir, stat, destination))
            .ok_or_else(|| {
                io::Error::new(io::ErrorKind::InvalidData, "Where have we been inlined to?")
            })?;
        // Upstream removes this old membership and assigns the pointer directly.
        ir[edge].closure = Some(closure);
        ir[last].label_edges.shift_remove(&edge);
    }
    Ok(())
}

fn is_inlineable(ir: &Ir, sequence: StatId, index: usize) -> bool {
    let first = ir[sequence].stats[index];
    let preceding = ir[sequence].stats[index - 1];
    if ir[preceding].has_basic_succ_edge() {
        return false;
    }
    let incoming = first.get_predecessor_edges(ir, EdgeType::Break.mask());
    let [edge] = incoming.as_slice() else {
        return false;
    };
    let edge = &ir[*edge];
    if !same_catch_ranges(ir, edge.source, edge.destination) || !edge.can_inline {
        return false;
    }
    if !edge.explicit
        && !ir[sequence].stats[index..]
            .iter()
            .all(|&child| no_exit_labels(ir, child, sequence))
    {
        return false;
    }
    if let Some(parent) = ir[edge.source].parent
        && matches!(&ir[parent].kind, StatementKind::Switch(switch) if switch.cases.is_empty())
    {
        return false;
    }
    ir[preceding].first_successor().is_some()
}

fn same_catch_ranges(ir: &Ir, mut from: StatId, to: StatId) -> bool {
    while let Some(parent) = ir[from].parent {
        if parent.contains_statement_strict(ir, to) {
            return true;
        }
        match ir[parent].kind {
            StatementKind::Catch { .. } | StatementKind::CatchAll { .. }
                if ir[parent].first == Some(from) =>
            {
                return false;
            }
            StatementKind::Synchronized { .. } if ir[parent].stats[1] == from => return false,
            _ => {}
        }
        from = parent;
    }
    false
}

fn no_exit_labels(ir: &Ir, block: StatId, sequence: StatId) -> bool {
    ir[block].all_successors().iter().all(|&edge| {
        ir[edge].edge_type == EdgeType::Regular
            || matches!(ir[ir[edge].destination].kind, StatementKind::DummyExit)
            || sequence.contains_statement_strict(ir, ir[edge].destination)
    }) && ir[block]
        .stats
        .iter()
        .all(|&child| no_exit_labels(ir, child, sequence))
}
