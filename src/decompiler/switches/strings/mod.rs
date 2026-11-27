//! Restore string selectors and literal labels from lowered string switches.

mod cases;
mod shape;

use std::io;

use self::cases::{merge_duplicate_cases, restore_split_labels, unwrap_merged_cases};
use self::shape::{Shape, StringSwitch};
use super::{switch, switch_head, switch_mut};
use crate::decompiler::exps::{Expr, ExprKind};
use crate::decompiler::ir::{ExprId, Ir, StatId};
use crate::decompiler::stats::{IfStatement, STATEDGE_ALL, Statement, StatementKind};
use crate::engine::{Cx, counter_container::CounterContainer};

pub(super) fn simplify(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    stat: StatId,
    selector: ExprId,
) -> io::Result<bool> {
    let Some(info) = StringSwitch::match_shape(cx, stat) else {
        return Ok(false);
    };
    let ExprKind::Invocation(invocation) = &cx.ir[selector].kind else {
        unreachable!("String switch selector must call hashCode");
    };
    let instance = invocation
        .instance
        .expect("String hashCode has no receiver");
    let (target_head, previous) = switch_head(&cx.ir, info.target).unwrap();
    Expr::replace(&mut cx.ir, target_head, previous, instance);

    if matches!(info.shape, Shape::Merged) {
        if !unwrap_merged_cases(&mut cx.ir, info.first) {
            return Ok(false);
        }
        merge_duplicate_cases(cx, info.first);
    } else {
        restore_split_labels(cx, counters, info);
        replace_split_switch(&mut cx.ir, counters, info)?;
    }
    remove_synthetic_dup(cx, info);
    Ok(true)
}

fn replace_split_switch(
    ir: &mut Ir,
    counters: &mut CounterContainer,
    info: StringSwitch,
) -> io::Result<()> {
    let first_head = info.first.get_basic_head(ir);
    let first_expressions = ir[first_head].exprents;
    if let Some(list) = first_expressions {
        ir[list].pop();
    }
    disconnect_predecessors(ir, first_head);
    for edge in first_head.get_successor_edges(ir, STATEDGE_ALL) {
        first_head.remove_successor(ir, edge);
    }

    if let (Some(source), Some(target)) = (
        first_expressions,
        ir[info.target.get_basic_head(ir)].exprents,
    ) {
        let expressions = std::mem::take(&mut ir[source]);
        if source != target {
            ir[target].extend(expressions);
        }
    }
    let replacement = if matches!(info.shape, Shape::InlineSplit) {
        ir[info.target]
            .parent
            .filter(|&parent| matches!(ir[parent].kind, StatementKind::Sequence))
            .unwrap_or(info.target)
    } else {
        first_head
    };
    disconnect_predecessors(ir, replacement);
    info.first.replace_with(ir, replacement);

    if let Shape::NullableSplit { null_check, .. } = info.shape {
        let replaced = Statement::new_empty_basic_block(ir, counters);
        null_check.replace_with(ir, replaced);
        let labels: Vec<_> = ir[replaced].label_edges.iter().copied().collect();
        for (index, &edge) in labels.iter().enumerate() {
            info.target.remove_predecessor(ir, edge);
            let modifies_label_set = ir[edge].closure == Some(replaced);
            edge.remove_closure(ir);
            // HashSet's iterator checks for modifications on its next advance.
            if modifies_label_set && index + 1 < labels.len() {
                return Err(io::Error::other(
                    "java.util.ConcurrentModificationException",
                ));
            }
        }
    }

    for edge in info.target.get_predecessor_edges(ir, STATEDGE_ALL) {
        let source = ir[edge].source;
        if source != first_head
            && (source == info.first || info.first.contains_statement_strict(ir, source))
        {
            source.remove_successor(ir, edge);
        }
    }
    Ok(())
}

fn disconnect_predecessors(ir: &mut Ir, stat: StatId) {
    for edge in stat.get_predecessor_edges(ir, STATEDGE_ALL) {
        stat.remove_predecessor(ir, edge);
    }
}

fn remove_synthetic_dup(cx: &mut Cx, info: StringSwitch) {
    let Some(dup) = info.synthetic_dup(cx) else {
        return;
    };
    let ExprKind::SwitchHead { value, .. } = &mut cx.ir[dup.head].kind else {
        unreachable!();
    };
    *value = dup.replacement;
    if !matches!(info.shape, Shape::NullableSplit { .. }) {
        cx.ir[dup.list].remove(dup.index);
    }
}

fn default_case(ir: &Ir, stat: StatId) -> Option<StatId> {
    switch(ir, stat)
        .default_edge
        .map(|edge| ir[edge].destination)
}

fn condition(ir: &Ir, branch: IfStatement) -> ExprId {
    let head = ir[branch.head_exprents.expect("Missing conditional header")][0];
    let ExprKind::If { condition } = ir[head].kind else {
        unreachable!("Unexpected conditional header");
    };
    condition
}
