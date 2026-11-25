// Copyright 2000-2020 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! MergeHelper.enhanceLoops. A change to the loop type restarts this pass
//! after the rest of the tree has been visited.

use std::io;

use super::{counted::match_for, foreach::match_for_each, inherit_offsets};
use crate::decompiler::decompose::finish::{condense_sequences, destroy_and_flatten_statement};
use crate::decompiler::exps::Expr;
use crate::decompiler::ir::{EdgeId, ExprId, ExprKind, Ir, StatId};
use crate::decompiler::labels::{is_direct_path, low_closures};
use crate::decompiler::stats::{
    LoopType, Statement, StatementKind,
    stat_edge::{EdgeType, StatEdge},
};
use crate::engine::{Cx, counter_container::CounterContainer};

pub(crate) fn enhance(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    root: StatId,
) -> io::Result<bool> {
    let cx = &mut *cx.enter_method(counters);
    let mut changed = false;
    while enhance_tree(cx, counters, root, root)? {
        changed = true;
    }
    if changed {
        condense_sequences(cx, counters, root);
    }
    Ok(changed)
}

fn enhance_tree(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    root: StatId,
    stat: StatId,
) -> io::Result<bool> {
    let mut changed = false;
    let children = cx.ir[stat].stats.to_vec();
    for child in children {
        if cx.ir[child].exprents.is_none() {
            changed |= enhance_tree(cx, counters, root, child)?;
        }
    }
    let StatementKind::Do(header) = cx.ir[stat].kind else {
        return Ok(changed);
    };
    let can_promote = match header.ty {
        LoopType::Infinite => match_while(cx, counters, stat),
        LoopType::While => true,
        _ => false,
    };
    if can_promote && !match_for_each(cx, root, stat)? {
        match_for(cx, counters, root, stat);
    }
    let StatementKind::Do(current) = cx.ir[stat].kind else {
        unreachable!()
    };
    Ok(changed || current.ty != header.ty)
}

fn match_while(cx: &mut Cx, counters: &mut CounterContainer, stat: StatId) -> bool {
    let ir = &cx.ir;
    let mut first = ir[stat].first.unwrap();
    while matches!(ir[first].kind, StatementKind::Sequence) {
        first = ir[first].first.unwrap();
    }
    let StatementKind::If(branch) = ir[first].kind else {
        return false;
    };
    let head = ir[first].first.unwrap();
    if branch.has_else || !ir[ir[head].exprents.unwrap()].is_empty() {
        return false;
    }

    let if_edge = branch.if_edge.unwrap();
    let head_expr = ir[branch.head_exprents.unwrap()][0];
    let exits_on_true = branch.if_stat.is_none()
        && (is_direct_path(&cx.ir, stat, cx.ir[if_edge].destination)
            || add_continue_or_break(&mut cx.ir, stat, if_edge));
    let else_edge = cx.ir[first]
        .first_successor()
        .expect("Loop condition has no successor");
    let exit = if exits_on_true {
        if_edge
    } else if is_direct_path(&cx.ir, stat, cx.ir[else_edge].destination) {
        else_edge
    } else {
        return false;
    };

    stat.set_loop_type(&mut cx.ir, LoopType::While);
    move_condition(cx, counters, stat, head_expr, exits_on_true);
    let ir = &mut cx.ir;
    if_edge.remove(ir);
    else_edge.remove(ir);
    if ir[stat].all_successors().is_empty() {
        ir[exit].source = stat;
        if ir[exit].closure == Some(stat) {
            ir[exit].closure = ir[stat].parent;
        }
        stat.add_successor(ir, exit);
    }

    if exits_on_true {
        if ir[stat].first == Some(first) {
            let empty = Statement::new_empty_basic_block(ir, counters);
            stat.replace_statement(ir, first, empty);
            let edge = StatEdge::new(ir, EdgeType::Continue, empty, stat, Some(stat));
            empty.add_successor(ir, edge);
        } else {
            let sequence = ir[first].parent.unwrap();
            let id = ir[first].id;
            ir[sequence].stats.remove_with_key(&id);
            if let Some(&next) = ir[sequence].stats.first() {
                ir[sequence].first = Some(next);
            } else {
                let parent = ir[sequence].parent.unwrap();
                destroy_and_flatten_statement(cx, counters, parent, sequence);
            }
        }
    } else if let Some(body) = branch.if_stat {
        first.replace_with(ir, body);
        for predecessor in ir[exit]
            .destination
            .get_predecessor_edges(ir, EdgeType::Break.mask())
        {
            if ir[predecessor]
                .closure
                .is_some_and(|closure| stat.contains_statement_strict(ir, closure))
            {
                stat.add_labeled_edge(ir, predecessor);
            }
        }
        low_closures(ir, stat);
    } else {
        let empty = Statement::new_empty_basic_block(ir, counters);
        ir[if_edge].source = empty;
        empty.add_successor(ir, if_edge);
        stat.replace_statement(ir, first, empty);
    }
    true
}

/// Copy the entire IfExprent before transferring its condition. The wrapper
/// also consumes an expression ID in the original pass.
fn move_condition(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    stat: StatId,
    head: ExprId,
    negate: bool,
) {
    let copied = Expr::copy(cx, counters, head);
    let ir = &mut cx.ir;
    if negate {
        Expr::negate_if(ir, counters, copied);
    }
    let ExprKind::If { condition } = ir[copied].kind else {
        unreachable!()
    };
    let StatementKind::Do(header) = ir[stat].kind else {
        unreachable!()
    };
    if let Some(old) = header.condition(ir) {
        inherit_offsets(ir, condition, old);
    }
    inherit_offsets(ir, condition, head);
    stat.set_loop_condition(ir, condition);
}

fn add_continue_or_break(ir: &mut Ir, stat: StatId, if_edge: EdgeId) -> bool {
    let outer =
        std::iter::successors(ir[stat].parent, |&parent| ir[parent].parent).find(|&parent| {
            matches!(
                ir[parent].kind,
                StatementKind::Switch(_) | StatementKind::Do(_)
            )
        });
    let Some(outer) = outer else { return false };
    if matches!(ir[outer].kind, StatementKind::Do(header) if header.ty == LoopType::Infinite) {
        return false;
    }
    let parent = ir[stat].parent.unwrap();
    if matches!(ir[parent].kind, StatementKind::Sequence) && ir[parent].stats.last() != Some(&stat)
    {
        return false;
    }
    let destination = ir[if_edge].destination;
    let kind = if destination == outer {
        EdgeType::Continue
    } else if is_direct_path(ir, outer, destination) {
        EdgeType::Break
    } else {
        return false;
    };
    let edge = StatEdge::new(ir, kind, stat, destination, Some(outer));
    stat.add_successor(ir, edge);
    true
}
