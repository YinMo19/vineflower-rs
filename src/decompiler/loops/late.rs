//! Recover post-test loops and move return blocks out of infinite loops.

use std::io;

use super::{counted::remove_last_empty, enhance::move_condition};
use crate::decompiler::decompose::finish::condense_sequences;
use crate::decompiler::ir::{ExprKind, Ir, StatId};
use crate::decompiler::labels::is_direct_path;
use crate::decompiler::stats::{
    LoopType, STATEDGE_ALL, Statement, StatementKind,
    stat_edge::{EdgeType, StatEdge},
};
use crate::engine::{Cx, counter_container::CounterContainer};

pub(crate) fn make_do_while(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    root: StatId,
) -> io::Result<bool> {
    let changed = make_do_while_tree(cx, counters, root);
    if changed {
        condense_sequences(cx, counters, root);
    }
    Ok(changed)
}

fn make_do_while_tree(cx: &mut Cx, counters: &mut CounterContainer, stat: StatId) -> bool {
    let mut changed = false;
    for index in 0..cx.ir[stat].stats.len() {
        changed |= make_do_while_tree(cx, counters, cx.ir[stat].stats[index]);
    }
    if infinite(&cx.ir, stat) {
        changed |= match_do_while(cx, counters, stat);
    }
    changed
}

fn infinite(ir: &Ir, stat: StatId) -> bool {
    matches!(ir[stat].kind, StatementKind::Do(header) if header.ty == LoopType::Infinite)
}

fn match_do_while(cx: &mut Cx, counters: &mut CounterContainer, stat: StatId) -> bool {
    let ir = &cx.ir;
    let mut last = ir[stat].first.unwrap();
    while matches!(ir[last].kind, StatementKind::Sequence) {
        last = *ir[last].stats.last().unwrap();
    }
    let StatementKind::If(branch) = ir[last].kind else {
        return false;
    };
    if branch.has_else || branch.if_stat.is_some() {
        return false;
    }
    let if_edge = branch.if_edge.unwrap();
    let else_edge = ir[last]
        .first_successor()
        .expect("Loop tail if has no successor");
    let (exit, negate) = match (ir[if_edge].edge_type, ir[else_edge].edge_type) {
        (EdgeType::Break, EdgeType::Continue) if ir[else_edge].closure == Some(stat) => {
            (if_edge, true)
        }
        (EdgeType::Continue, EdgeType::Break) if ir[if_edge].closure == Some(stat) => {
            (else_edge, false)
        }
        (EdgeType::Continue, EdgeType::Continue)
            if ir[else_edge].closure == Some(stat) && is_last_in_loop(ir, stat) =>
        {
            (if_edge, true)
        }
        _ => return false,
    };
    if !is_direct_path(ir, stat, ir[exit].destination)
        || stat
            .get_predecessor_edges(ir, EdgeType::Continue.mask())
            .iter()
            .any(|&edge| ir[edge].source != last)
    {
        return false;
    }

    let head_expr = ir[branch.head_exprents.unwrap()][0];
    stat.set_loop_type(&mut cx.ir, LoopType::DoWhile);
    move_condition(cx, counters, stat, head_expr, negate);

    let ir = &mut cx.ir;
    else_edge.remove(ir);
    let head = ir[last].first.unwrap();
    let expressions = ir[head].exprents.unwrap();
    if ir[expressions].is_empty() {
        if_edge.remove(ir);
        remove_last_empty(ir, counters, stat, last);
    } else if ir[stat].stats.len() == 1 && ir[if_edge].edge_type == EdgeType::Continue {
        last.replace_with(ir, head);
    } else {
        ir[last].exprents = Some(expressions);
        let edge = StatEdge::new(ir, EdgeType::Continue, last, stat, None);
        last.add_successor(ir, edge);
        stat.add_labeled_edge(ir, edge);
    }

    if ir[stat].all_successors().is_empty() {
        ir[exit].source = stat;
        if ir[exit].closure == Some(stat) {
            ir[exit].closure = ir[stat].parent;
        }
        stat.add_successor(ir, exit);
    }
    true
}

fn is_last_in_loop(ir: &Ir, mut stat: StatId) -> bool {
    while let Some(parent) = ir[stat].parent {
        if !matches!(ir[parent].kind, StatementKind::Sequence) {
            return matches!(ir[parent].kind, StatementKind::Do(_));
        }
        if ir[parent].stats.last() != Some(&stat) {
            return false;
        }
        stat = parent;
    }
    false
}

pub(crate) fn condense_returns(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    root: StatId,
) -> io::Result<bool> {
    let changed = condense_returns_tree(&mut cx.ir, counters, root);
    if changed {
        condense_sequences(cx, counters, root);
    }
    Ok(changed)
}

fn condense_returns_tree(ir: &mut Ir, counters: &mut CounterContainer, stat: StatId) -> bool {
    let mut changed = infinite(ir, stat) && condense_return(ir, counters, stat);
    let children = ir[stat].stats.to_vec();
    for child in children {
        changed |= condense_returns_tree(ir, counters, child);
    }
    changed
}

fn condense_return(ir: &mut Ir, counters: &mut CounterContainer, stat: StatId) -> bool {
    let first = ir[stat].first.unwrap();
    if !matches!(ir[first].kind, StatementKind::Sequence)
        || !stat
            .get_successor_edges(ir, EdgeType::Regular.mask())
            .is_empty()
    {
        return false;
    }
    let Some(start) = extractable_from_loop(ir, first, stat) else {
        return false;
    };
    let first_body = ir[first].stats[0];
    let last_body = *ir[first].stats.last().unwrap();
    let previous = ir[first].stats[start - 1];
    let StatementKind::If(branch) = ir[first_body].kind else {
        return false;
    };
    let head = first_body.get_basic_head(ir);
    if branch.has_else || !ir[ir[head].exprents.unwrap()].is_empty() {
        return false;
    }
    if !last_body
        .get_successor_edges(ir, EdgeType::Break.mask())
        .first()
        .is_some_and(|&edge| {
            matches!(
                ir[ir[edge].destination].kind,
                StatementKind::DummyExit { .. }
            )
        })
        || !continues_loop(ir, first_body, stat)
    {
        return false;
    }

    let mut extracted = ir[first].stats[start..].to_vec();
    for &child in &extracted {
        for edge in child.get_predecessor_edges(ir, STATEDGE_ALL) {
            match ir[edge].edge_type {
                EdgeType::Regular if ir[edge].source == previous => edge.remove(ir),
                EdgeType::Break if stat.contains_statement_strict(ir, ir[edge].source) => {
                    stat.add_labeled_edge(ir, edge);
                }
                _ => {}
            }
        }
    }

    extracted.insert(0, stat);
    let sequence = Statement::new_sequence(ir, counters, &extracted);
    for &child in &extracted {
        let id = ir[child].id;
        ir[first].stats.remove_with_key(&id);
    }
    stat.replace_with(ir, sequence);

    let labels: Vec<_> = ir[sequence].label_edges.iter().copied().collect();
    for edge in labels {
        stat.add_labeled_edge(ir, edge);
    }
    for edge in sequence.get_predecessor_edges(ir, EdgeType::Continue.mask()) {
        if stat.contains_statement_strict(ir, ir[edge].source) {
            edge.change_destination(ir, stat);
        }
    }
    sequence.set_all_parent(ir);

    let edge = StatEdge::new(ir, EdgeType::Regular, stat, extracted[1], None);
    stat.add_successor(ir, edge);

    let body = branch.if_stat.expect("Loop header if has no body");
    first.replace_with(ir, body);
    let edge = branch.if_edge.unwrap();
    // The Java rewrite removes this edge through its destination.
    ir[edge].destination.remove_successor(ir, edge);
    ir[stat].first = Some(body);
    stat.set_all_parent(ir);
    stat.set_loop_type(ir, LoopType::While);
    let head_expr = ir[branch.head_exprents.unwrap()][0];
    let ExprKind::If { condition } = ir[head_expr].kind else {
        unreachable!("If header must be an IfExprent");
    };
    stat.set_loop_condition(ir, condition);
    body.set_all_parent(ir);
    true
}

fn extractable_from_loop(ir: &Ir, sequence: StatId, stat: StatId) -> Option<usize> {
    let mut start = None;
    for (index, &child) in ir[sequence].stats.iter().enumerate() {
        if continues_loop(ir, child, stat) || index == 0 {
            continue;
        }
        let previous = ir[sequence].stats[index - 1];
        if let [edge] = ir[previous].all_successors()
            && ir[*edge].edge_type == EdgeType::Regular
            && ir[*edge].destination == child
        {
            start.get_or_insert(index);
        }
    }
    start
}

fn continues_loop(ir: &Ir, stat: StatId, loop_: StatId) -> bool {
    stat.edges_leaving(ir, stat, false)
        .iter()
        .any(|&edge| ir[edge].edge_type == EdgeType::Continue && ir[edge].destination == loop_)
}
