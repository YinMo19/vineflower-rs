// SPDX-License-Identifier: Apache-2.0

//! Recover switch result expressions and their yielding branches.

use std::io;

use indexmap::IndexMap;

use crate::decompiler::decompose::finish::condense_sequences;
use crate::decompiler::exps::{ExitType, Expr, ExprKind, STACK_BASE, Variable};
use crate::decompiler::ir::{ExprId, Ir, StatId};
use crate::decompiler::stats::{
    STATEDGE_ALL, Statement, StatementKind,
    stat_edge::{EdgeType, StatEdge},
};
use crate::engine::{Cx, counter_container::CounterContainer};

pub(crate) fn process(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    root: StatId,
) -> io::Result<bool> {
    if !cx.options.decompile_switch_expressions
        || !root
            .method(&cx.ir)
            .bytecode_version
            .has_switch_expressions()
    {
        return Ok(false);
    }
    let changed = process_tree(cx, counters, root, root);
    if changed {
        condense_sequences(cx, counters, root);
    }
    Ok(changed)
}

fn process_tree(cx: &mut Cx, counters: &mut CounterContainer, root: StatId, stat: StatId) -> bool {
    let mut changed = false;
    let children = cx.ir[stat].stats.to_vec();
    for child in children {
        changed |= process_tree(cx, counters, root, child);
    }
    if matches!(cx.ir[stat].kind, StatementKind::Switch(_)) && !cx.ir[stat].phantom {
        changed |= process_switch(cx, counters, root, stat);
    }
    changed
}

fn process_switch(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    root: StatId,
    stat: StatId,
) -> bool {
    let Some(result) = switch_result(&cx.ir, root, stat) else {
        return false;
    };
    let Some(regular) = stat
        .get_successor_edges(&cx.ir, EdgeType::Regular.mask())
        .first()
        .copied()
    else {
        return false;
    };
    let successor = cx.ir[regular].destination;
    let successor = ensure_basic_successor(&mut cx.ir, counters, stat, successor);
    cx.ir[stat].phantom = true;

    let variable = Expr::variable(&cx.ir, result).unwrap();
    let slot = variable.index;
    let processor = variable.processor;
    let StatementKind::Switch(switch) = &cx.ir[stat].kind else {
        unreachable!();
    };
    let cases: Vec<_> = switch.cases.iter().map(|case| case.statement).collect();
    for case in cases {
        let mut replacements = IndexMap::new();
        find_replacements(cx, counters, case, slot, &mut replacements);
        if !replacements.is_empty() {
            replace_assignments(cx, case, &replacements);
        }
    }

    let mut result_var = Variable::new(slot, Expr::expr_type(cx, result));
    result_var.processor = processor;
    result_var.stack = true;
    let left = Expr::new(&mut cx.ir, counters, ExprKind::Variable(result_var), None);
    let var_type = Expr::expr_type(cx, result);
    let right = Expr::new(
        &mut cx.ir,
        counters,
        ExprKind::Switch {
            backing: stat,
            var_type,
            fallthrough: false,
            standalone: false,
        },
        None,
    );
    let assignment = Expr::new(
        &mut cx.ir,
        counters,
        ExprKind::Assignment {
            left,
            right,
            compound: None,
        },
        None,
    );
    move_stack_assignments(&mut cx.ir, stat, successor, assignment);
    true
}

fn switch_result(ir: &Ir, root: StatId, stat: StatId) -> Option<ExprId> {
    let StatementKind::Switch(switch) = &ir[stat].kind else {
        unreachable!();
    };
    let head = ir[switch.head_exprents.expect("Missing switch header")][0];
    let ExprKind::SwitchHead { value, .. } = ir[head].kind else {
        unreachable!("Switch header must be a SwitchHeadExprent");
    };
    if matches!(&ir[value].kind, ExprKind::Invocation(invoke)
        if invoke.name == "hashCode" && invoke.classname.as_deref() == Some("java/lang/String"))
    {
        return None;
    }

    let (next, break_jumps) = find_next(ir, root, stat)?;
    let cases = switch.cases.iter().map(|case| case.statement);
    for branch in break_jumps.iter().copied().chain(cases.clone()) {
        if !ir[branch].has_basic_succ_edge() {
            continue;
        }
        let breaks = branch.get_successor_edges(ir, EdgeType::Break.mask());
        let first = &ir[*breaks.first()?];
        if !first
            .closure
            .is_some_and(|closure| closure == stat || stat.contains_statement_strict(ir, closure))
            && !matches!(ir[first.destination].kind, StatementKind::DummyExit)
        {
            return None;
        }
    }

    for (index, case) in cases.clone().enumerate() {
        let last = index == switch.cases.len() - 1;
        let mut found_break = false;
        for edge in case.edges_leaving(ir, stat, true) {
            let edge = &ir[edge];
            if edge.edge_type != EdgeType::Break {
                continue;
            }
            if (edge.destination != next
                && !matches!(ir[edge.destination].kind, StatementKind::DummyExit))
                || (!edge.explicit && !last)
            {
                return None;
            }
            found_break = true;
        }
        if !found_break {
            return None;
        }
    }

    if !switch
        .cases
        .iter()
        .flat_map(|case| &case.edges)
        .any(|&edge| Some(edge) == switch.default_edge)
    {
        return None;
    }
    let result = find_relevant_var(ir, &break_jumps)?;
    for case in cases {
        if case
            .edges_leaving(ir, case, false)
            .iter()
            .any(|&edge| ir[edge].edge_type == EdgeType::Continue)
        {
            return None;
        }
    }
    Some(result)
}

fn find_next(ir: &Ir, root: StatId, stat: StatId) -> Option<(StatId, Vec<StatId>)> {
    let regular = EdgeType::Regular.mask();
    let edge = std::iter::successors(Some(stat), |&ancestor| ir[ancestor].parent)
        .take_while(|&ancestor| ir[ancestor].parent.is_some())
        .find_map(|ancestor| ancestor.get_successor_edges(ir, regular).first().copied())?;
    let next = ir[edge].destination;
    let StatementKind::Root { dummy_exit, .. } = ir[root].kind else {
        unreachable!();
    };
    let mask = EdgeType::Break.mask();
    let sources = next
        .get_predecessor_edges(ir, mask)
        .into_iter()
        .chain(dummy_exit.get_predecessor_edges(ir, mask))
        .map(|edge| ir[edge].source)
        .filter(|&source| source == stat || stat.contains_statement_strict(ir, source))
        .collect();
    Some((next, sources))
}

fn find_relevant_var(ir: &Ir, break_jumps: &[StatId]) -> Option<ExprId> {
    let mut candidate = None;
    let mut single_assignment = false;
    for &stat in break_jumps {
        let Some(list) = ir[stat].exprents else {
            continue;
        };
        let Some(&last) = ir[list].last() else {
            continue;
        };
        if let ExprKind::Exit { kind, .. } = ir[last].kind {
            if kind == ExitType::Throw {
                continue;
            }
            return None;
        }

        // The result is the last assignment, and at least one branch must
        // have only one candidate in its trailing assignments.
        let var = assignment_target(ir, last)?;
        let variable = Expr::variable(ir, var).unwrap();
        let pair = variable.pair();
        let same_var = candidate.get_or_insert((var, pair)).1 == pair;
        if !same_var {
            return None;
        }
        let preceding = ir[list]
            .iter()
            .rev()
            .nth(1)
            .and_then(|&expr| assignment_target(ir, expr));
        single_assignment |= variable.index >= STACK_BASE || preceding.is_none();
    }
    candidate
        .filter(|_| single_assignment)
        .map(|(variable, _)| variable)
}

fn assignment_target(ir: &Ir, expr: ExprId) -> Option<ExprId> {
    match ir[expr].kind {
        ExprKind::Assignment { left, .. } if Expr::variable(ir, left).is_some() => Some(left),
        _ => None,
    }
}

fn ensure_basic_successor(
    ir: &mut Ir,
    counters: &mut CounterContainer,
    switch: StatId,
    successor: StatId,
) -> StatId {
    if matches!(ir[successor].kind, StatementKind::BasicBlock { .. }) {
        return successor;
    }

    let block = Statement::new_empty_basic_block(ir, counters);
    let sequence = Statement::new_sequence(ir, counters, &[switch, block]);
    switch.replace_with(ir, sequence);
    sequence.set_all_parent(ir);

    for edge in successor.get_predecessor_edges(ir, STATEDGE_ALL) {
        let source = ir[edge].source;
        if source == switch || switch.contains_statement_strict(ir, source) {
            let kind = ir[edge].edge_type;
            edge.remove(ir);
            let edge = StatEdge::new(ir, kind, source, block, Some(switch));
            source.add_successor(ir, edge);
        }
    }
    let edge = StatEdge::new(ir, EdgeType::Regular, block, successor, Some(sequence));
    block.add_successor(ir, edge);
    block
}

fn find_replacements(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    stat: StatId,
    slot: i32,
    replacements: &mut IndexMap<ExprId, ExprId>,
) {
    if let Some(list) = cx.ir[stat].exprents {
        for index in 0..cx.ir[list].len() {
            let expr = cx.ir[list][index];
            if let ExprKind::Assignment { left, right, .. } = cx.ir[expr].kind
                && Expr::variable(&cx.ir, left).is_some_and(|var| var.index == slot)
            {
                let return_type = Expr::expr_type(cx, expr);
                let replacement = Expr::new(
                    &mut cx.ir,
                    counters,
                    ExprKind::Yield {
                        value: right,
                        return_type,
                    },
                    None,
                );
                replacements.insert(expr, replacement);
            }
        }
    }
    for index in 0..cx.ir[stat].stats.len() {
        find_replacements(cx, counters, cx.ir[stat].stats[index], slot, replacements);
    }
}

fn replace_assignments(cx: &mut Cx, stat: StatId, replacements: &IndexMap<ExprId, ExprId>) {
    if matches!(cx.ir[stat].kind, StatementKind::BasicBlock { .. }) {
        let list = cx.ir[stat].exprents.expect("Missing case expressions");
        for expr in &mut cx.ir[list] {
            if let Some(&replacement) = replacements.get(expr) {
                *expr = replacement;
            }
        }
    } else {
        for (&old, &new) in replacements {
            stat.replace_header(cx, old, new);
        }
    }
    for index in 0..cx.ir[stat].stats.len() {
        replace_assignments(cx, cx.ir[stat].stats[index], replacements);
    }
}

fn move_stack_assignments(ir: &mut Ir, stat: StatId, successor: StatId, assignment: ExprId) {
    let head = ir[stat].first.unwrap();
    let mut prefix = Vec::new();
    if let Some(list) = ir[head].exprents {
        let mut expressions = std::mem::take(&mut ir[list]);
        expressions.retain(|&expr| {
            let stack = assignment_target(ir, expr)
                .and_then(|left| Expr::variable(ir, left))
                .is_some_and(|var| var.stack);
            if stack {
                prefix.push(expr);
            }
            !stack
        });
        ir[list] = expressions;
    }
    prefix.push(assignment);
    let list = ir[successor]
        .exprents
        .expect("Missing successor expressions");
    ir[list].splice(..0, prefix);
}
