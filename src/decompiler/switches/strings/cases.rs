//! Recover string labels and the case targets attached to them.

use rustc_hash::FxHashMap;

use crate::decompiler::exps::{ConstantValue, ExitType, Expr, ExprKind};
use crate::decompiler::ir::{ExprId, Ir, StatId};
use crate::decompiler::stats::{
    STATEDGE_ALL, StatementKind, SwitchCase,
    stat_edge::{EdgeType, StatEdge},
};
use crate::engine::{Cx, counter_container::CounterContainer};
use crate::types::VarType;

use super::shape::{Shape, StringSwitch, remove_condition_wrapper};
use super::{condition, switch, switch_mut};

pub(super) fn restore_split_labels(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    info: StringSwitch,
) {
    let mut labels = string_labels(&cx.ir, info.first);
    if let Shape::NullableSplit { assignment, .. } = info.shape {
        let (_, right) = cx.ir[assignment].as_assignment().unwrap();
        let intermediate = integer(&cx.ir, right);
        let null = Expr::new(
            &mut cx.ir,
            counters,
            Expr::constant(VarType::VARTYPE_NULL, ConstantValue::Null, false),
            None,
        );
        labels.entry(intermediate).or_default().push(null);
    }

    let ir = &mut cx.ir;
    let mut restored = Vec::new();
    let default = switch(ir, info.target).default_edge;
    for index in 0..switch(ir, info.target).cases.len() {
        let mut literals = Vec::new();
        let mut label = 0;
        while label < switch(ir, info.target).cases[index].values.len() {
            let case = &switch(ir, info.target).cases[index];
            let edge = case.edges[label];
            let intermediate = case.values[label].and_then(|value| {
                matches!(ir[value].kind, ExprKind::Constant { .. }).then(|| integer(ir, value))
            });
            if let Some(strings) = intermediate.and_then(|value| labels.get(&value)) {
                literals.extend(strings.iter().copied().map(Some));
            } else if default.is_some_and(|default| {
                edge != default && ir[edge].destination == ir[default].destination
            }) {
                // tableswitch padding still targets default. Only its case
                // table entries are removed by the Java rewrite.
                let case = &mut switch_mut(ir, info.target).cases[index];
                case.edges.remove(label);
                case.values.remove(label);
                continue;
            } else {
                literals.push(None);
            }
            label += 1;
        }
        restored.push(literals);
    }
    for (case, values) in switch_mut(ir, info.target).cases.iter_mut().zip(restored) {
        case.values = values;
    }
}

fn string_labels(ir: &Ir, first: StatId) -> FxHashMap<i32, Vec<ExprId>> {
    let mut mapping: FxHashMap<i32, Vec<ExprId>> = FxHashMap::default();
    for case in &switch(ir, first).cases {
        let mut branch = Some(case.statement);
        while let Some(stat) = branch {
            let StatementKind::If(if_) = ir[stat].kind else {
                break;
            };
            let cond = remove_condition_wrapper(ir, condition(ir, if_), false);
            if let ExprKind::Invocation(invoke) = &ir[cond].kind
                && let [label] = invoke.parameters.as_slice()
            {
                let body = if_.if_stat.expect("String equality branch has no body");
                let Some(list) = ir[body].exprents else {
                    break;
                };
                let expression = ir[list][0];
                if let Some((_, right)) = ir[expression].as_assignment() {
                    let intermediate = integer(ir, right);
                    mapping.entry(intermediate).or_default().push(*label);
                } else if matches!(ir[expression].kind, ExprKind::Exit { .. }) {
                    for &value in &case.values {
                        let hash = integer(ir, value.expect("Missing string hash label"));
                        mapping.entry(hash).or_default().push(*label);
                    }
                }
            }
            branch = if_.else_stat;
        }
    }
    mapping
}

pub(super) fn unwrap_merged_cases(ir: &mut Ir, stat: StatId) -> bool {
    let mut index = 0;
    let mut processed = 0;
    while index < switch(ir, stat).cases.len() {
        let root = switch(ir, stat).cases[index].statement;
        index += 1;
        let StatementKind::If(branch) = ir[root].kind else {
            continue;
        };
        let body = branch.if_stat.expect("String equality branch has no body");
        let Some(expressions) = ir[body].exprents else {
            continue;
        };
        let [expression] = ir[expressions].as_slice() else {
            continue;
        };
        if !matches!(
            ir[*expression].kind,
            ExprKind::Exit {
                kind: ExitType::Return,
                ..
            }
        ) {
            continue;
        }

        remove_case(ir, stat, processed);
        if let Some(&edge) = root
            .get_successor_edges(ir, EdgeType::Regular.mask())
            .first()
        {
            edge.remove(ir);
        }

        let mut cursor = Some(root);
        while let Some(current) = cursor {
            let StatementKind::If(branch) = ir[current].kind else {
                unreachable!("String switch collision chain must use if statements");
            };
            let next = branch.else_stat;
            if next.is_some_and(|next| !matches!(ir[next].kind, StatementKind::If(_))) {
                panic!("String switch collision chain must use if statements");
            }
            if let Some(&edge) = current
                .get_successor_edges(ir, EdgeType::Break.mask())
                .first()
            {
                edge.remove(ir);
            }
            for edge in current
                .get_basic_head(ir)
                .get_successor_edges(ir, STATEDGE_ALL)
            {
                edge.remove(ir);
            }

            let cond = condition(ir, branch);
            let literals = match &ir[cond].kind {
                ExprKind::Function { operands, .. } => operands
                    .iter()
                    .filter_map(|&operand| match &ir[operand].kind {
                        ExprKind::Invocation(invoke) => Some(Some(invoke.parameters[0])),
                        _ => None,
                    })
                    .collect(),
                ExprKind::Invocation(invoke) => vec![Some(invoke.parameters[0])],
                _ => return false,
            };
            let body = branch.if_stat.expect("String equality branch has no body");
            add_case(ir, stat, processed, body, literals);
            processed += 1;
            cursor = next;
        }
    }
    processed > 0
}

pub(super) fn merge_duplicate_cases(cx: &mut Cx, stat: StatId) {
    let mut index = 0;
    while index < switch(&cx.ir, stat).cases.len() {
        let body = switch(&cx.ir, stat).cases[index].statement;
        index += 1;
        let list = cx.ir[body].exprents;
        if list.is_some_and(|list| cx.ir[list].len() != 1) {
            continue;
        }
        let mut other = index;
        while other < switch(&cx.ir, stat).cases.len() {
            let next = switch(&cx.ir, stat).cases[other].statement;
            let first = cx.ir[next]
                .exprents
                .and_then(|list| cx.ir[list].first().copied());
            if !first.is_some_and(|expr| {
                let list = list.expect("String switch case has no expressions");
                Expr::equals(cx, cx.ir[list][0], expr)
            }) {
                other += 1;
                continue;
            }

            let case = &switch(&cx.ir, stat).cases[other];
            let values = case.values.clone();
            let edge = case.edges[0];
            let current = &mut switch_mut(&mut cx.ir, stat).cases[index - 1];
            current.values.extend(values);
            current.edges.push(edge);
            // The Java rewrite changes the endpoint before removing the old case.
            cx.ir[edge].destination = body;
            remove_case(&mut cx.ir, stat, other);
        }
    }
}

fn add_case(ir: &mut Ir, stat: StatId, index: usize, body: StatId, values: Vec<Option<ExprId>>) {
    // SwitchStatement.addCase inserts the case with the list's unkeyed API.
    ir[stat].stats.insert(index + 1, body);
    let head = stat.get_basic_head(ir);
    let edges = (0..values.len())
        .map(|_| {
            let edge = StatEdge::new(ir, EdgeType::Regular, head, body, None);
            head.add_successor(ir, edge);
            edge
        })
        .collect();
    switch_mut(ir, stat).cases.insert(
        index,
        SwitchCase {
            statement: body,
            edges,
            values,
        },
    );
    ir[body].parent = Some(stat);
}

fn remove_case(ir: &mut Ir, stat: StatId, index: usize) {
    let body = switch(ir, stat).cases[index].statement;
    for edge in body.get_predecessor_edges(ir, STATEDGE_ALL) {
        edge.remove(ir);
    }
    for edge in body.get_successor_edges(ir, STATEDGE_ALL) {
        edge.remove(ir);
    }
    let id = ir[body].id;
    ir[stat].stats.remove_with_key(&id);
    let case = switch_mut(ir, stat).cases.remove(index);
    for edge in case.edges {
        edge.remove(ir);
    }
}

fn integer(ir: &Ir, expr: ExprId) -> i32 {
    let ExprKind::Constant {
        value: ConstantValue::Integer(value),
        ..
    } = ir[expr].kind
    else {
        panic!("Expected an integer constant in a string switch");
    };
    value
}
