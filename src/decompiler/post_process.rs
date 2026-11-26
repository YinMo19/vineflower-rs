// Copyright 2000-2024 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Return and monitor rewrites after switch simplification.

use super::exps::{ExitType, Expr, ExprKind, Variable};
use super::ir::{ExprId, Ir, StatId, VarProcessorId};
use super::stats::StatementKind;
use crate::engine::{
    Cx,
    counter_container::{CounterContainer, VAR_COUNTER},
};
use crate::types::VarType;

fn dummy_exit(ir: &Ir, root: StatId) -> StatId {
    let StatementKind::Root { dummy_exit, .. } = ir[root].kind else {
        unreachable!()
    };
    dummy_exit
}

/// Adjust constants in exit operands using the declared return type. Java
/// reports a visit for every constant, including those already of this type.
pub(crate) fn adjust_returns(ir: &mut Ir, root: StatId, expected: &VarType) -> bool {
    let mut visited = false;
    for edge in ir[dummy_exit(ir, root)].all_predecessors().to_vec() {
        let source = ir[edge].source;
        let Some(&exit) = ir[source].exprents.and_then(|list| ir[list].last()) else {
            continue;
        };
        if !matches!(ir[exit].kind, ExprKind::Exit { .. }) {
            continue;
        }
        for expr in Expr::all_exprents(ir, exit, true, false) {
            visited |= super::exps::literal::adjust_const_type(ir, expr, expected);
        }
    }
    visited
}

pub(crate) fn remove_redundant_returns(ir: &mut Ir, root: StatId) -> bool {
    let dummy = dummy_exit(ir, root);
    let mut changed = false;
    for edge in ir[dummy].all_predecessors().to_vec() {
        if ir[edge].explicit {
            continue;
        }
        let Some(list) = ir[ir[edge].source].exprents else {
            continue;
        };
        let Some(&exit) = ir[list].last() else {
            continue;
        };
        if !matches!(
            ir[exit].kind,
            ExprKind::Exit {
                kind: ExitType::Return,
                value: None,
                ..
            }
        ) {
            continue;
        }
        if let Some(offsets) = ir[exit]
            .bytecode
            .clone()
            .filter(|set| set.iter().next().is_some())
        {
            let StatementKind::DummyExit { bytecode } = &mut ir[dummy].kind else {
                unreachable!()
            };
            match bytecode {
                Some(current) => current.union(&offsets),
                None => *bytecode = Some(offsets),
            }
        }
        ir[list].pop();
        changed = true;
    }
    changed
}

fn monitor(ir: &Ir, stat: StatId) -> Option<(ExprId, ExprId)> {
    let StatementKind::Synchronized {
        head_exprents: Some(head),
        ..
    } = ir[stat].kind
    else {
        return None;
    };
    let &expr = ir[head].first()?;
    let ExprKind::Monitor { value, .. } = ir[expr].kind else {
        return None;
    };
    Some((expr, value))
}

pub(crate) fn clean_monitors(cx: &mut Cx, stat: StatId) -> bool {
    let mut changed = false;
    for index in 0..cx.ir[stat].stats.len() {
        changed |= clean_monitors(cx, cx.ir[stat].stats[index]);
    }
    let ir = &cx.ir;
    let Some((monitor, value)) = monitor(ir, stat) else {
        return changed;
    };
    let parent = ir[stat].parent.unwrap();
    let list = ir[ir[stat].first.unwrap()].exprents.unwrap();
    for index in 0..ir[list].len() {
        let Some((local, rhs)) = ir[ir[list][index]].as_assignment() else {
            continue;
        };
        if Expr::variable(ir, local).is_none() {
            continue;
        }
        if Expr::equals(cx, local, value)
            && !Expr::is_var_referenced_in_stat(ir, local, parent, &[value])
        {
            let offsets = ir[value].bytecode.clone();
            Expr::add_offsets(&mut cx.ir, monitor, offsets.as_ref());
            Expr::replace(&mut cx.ir, monitor, value, rhs);
            cx.ir[list].remove(index);
            return true;
        }
        if Expr::equals(cx, rhs, value) && !Expr::is_var_referenced_in_stat(ir, local, parent, &[])
        {
            cx.ir[list].remove(index);
            return true;
        }
    }
    changed
}

/// SynchronizedHelper.insertSink records its effects in the expressions and
/// root comments. Its Java return flag stays false even after an insertion.
pub(crate) fn insert_monitor_sinks(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    root: StatId,
    owner: VarProcessorId,
    stat: StatId,
) {
    for index in 0..cx.ir[stat].stats.len() {
        insert_monitor_sinks(cx, counters, root, owner, cx.ir[stat].stats[index]);
    }
    let Some((monitor, value)) = monitor(&cx.ir, stat) else {
        return;
    };
    match &cx.ir[value].kind {
        ExprKind::Constant { var_type, .. }
            if *var_type != VarType::VARTYPE_STRING && !var_type.is_generic_type() =>
        {
            let index = counters.get_counter_and_increment(VAR_COUNTER);
            let var = Variable::in_method(index, VarType::VARTYPE_OBJECT, owner);
            cx.ir[owner]
                .versions
                .lower
                .insert(var.pair(), VarType::VARTYPE_OBJECT);
            let local = Expr::new(&mut cx.ir, counters, ExprKind::Variable(var), None);
            let offsets = cx.ir[value].bytecode.clone();
            let assignment = Expr::new(
                &mut cx.ir,
                counters,
                ExprKind::Assignment {
                    left: local,
                    right: value,
                    compound: None,
                },
                offsets,
            );
            Expr::replace(&mut cx.ir, monitor, value, assignment);
            cx.ir[root].add_comment(
                "$VF: Added assignment to ensure synchronized validity",
                false,
            );
        }
        ExprKind::Invocation(call) if call.is_boxing_call(cx) => {
            let ExprKind::Invocation(call) = &mut cx.ir[value].kind else {
                unreachable!()
            };
            call.can_ignore_boxing = false;
        }
        _ => {}
    }
}
