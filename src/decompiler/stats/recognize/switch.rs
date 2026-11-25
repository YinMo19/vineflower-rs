// Copyright 2000-2020 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

use indexmap::{IndexMap, IndexSet};
use rustc_hash::FxHashMap;

use super::dec_helper::{check_statement_exceptions, is_choice_statement};
use super::with_head;
use crate::decompiler::ir::{EdgeId, Expr, ExprId, ExprKind, Ir, StatId};
use crate::decompiler::stats::EdgeDirection::{Backward, Forward};
use crate::decompiler::stats::stat_edge::{EdgeType, StatEdge};
use crate::decompiler::stats::{
    LastBasicType, STATEDGE_DIRECT_ALL, Statement, StatementKind, SwitchCase, SwitchStatement,
};
use crate::engine::counter_container::CounterContainer;

pub(super) fn detect_switch(
    ir: &mut Ir,
    counters: &mut CounterContainer,
    head: StatId,
) -> Option<StatId> {
    if !matches!(ir[head].kind, StatementKind::BasicBlock { .. })
        || ir[head].last_basic_type != LastBasicType::Switch
    {
        return None;
    }

    let (post, statements) = is_choice_statement(ir, head)?;
    if statements.iter().any(|&stat| ir[stat].is_monitor_enter)
        || !check_statement_exceptions(ir, &statements)
    {
        return None;
    }

    let children: IndexSet<_> = head
        .get_neighbours(ir, EdgeType::Regular.mask(), Forward)
        .into_iter()
        .filter(|child| Some(*child) != post)
        .collect();
    let mut children: Vec<_> = children.into_iter().collect();
    children.sort_by_key(|&child| ir[child].id);

    let kind = StatementKind::Switch(SwitchStatement {
        default_edge: super::first_direct_edge(ir, head),
        ..SwitchStatement::default()
    });
    let mut statement = with_head(ir, counters, kind, head);
    statement.post = post;
    for child in children {
        statement.stats.add_with_key(child, ir[child].id);
    }
    Some(ir.stats.push(statement))
}

struct CaseGroup {
    statement: Option<StatId>,
    labels: Vec<usize>,
}

/// Sort switch cases and turn direct exits into case bodies. The graph's
/// successor order defines bytecode label indices, with the default moved last.
pub(super) fn sort_edges_and_nodes(ir: &mut Ir, counters: &mut CounterContainer, switch: StatId) {
    let StatementKind::Switch(data) = &ir[switch].kind else {
        unreachable!();
    };
    if data
        .cases
        .iter()
        .flat_map(|case| &case.values)
        .any(|value| {
            value.is_none_or(|expr| !matches!(ir[expr].kind, ExprKind::IntConstant { .. }))
        })
    {
        return;
    }

    let head = ir[switch].first.unwrap();
    let head_successors = head.get_successor_edges(ir, STATEDGE_DIRECT_ALL);
    let default_label = head_successors.len();
    let label_indices: FxHashMap<_, _> = head_successors
        .iter()
        .enumerate()
        .map(|(index, &edge)| (edge, if index == 0 { default_label } else { index }))
        .collect();
    let StatementKind::BasicBlock { block } = ir[head].kind else {
        unreachable!("Switch does not have a basic block as its head");
    };
    let instruction = ir[block].get_last_instruction().unwrap().clone();
    let values = &instruction.as_switch().values;

    let regular = EdgeType::Regular.mask();
    let mut cases: Vec<_> = ir[switch]
        .stats
        .iter()
        .skip(1)
        .map(|&stat| {
            let labels = ir[stat]
                .edge_view(Backward, regular)
                .iter()
                .filter(|&&edge| ir[edge].source == head)
                .map(|edge| label_indices[edge])
                .collect();
            CaseGroup {
                statement: Some(stat),
                labels,
            }
        })
        .collect();

    // Cases leaving the switch directly need one body per destination and edge type.
    let mut exit_groups: IndexMap<_, Vec<_>> = IndexMap::new();
    for edge in head.get_successor_edges(ir, EdgeType::Break.mask() | EdgeType::Continue.mask()) {
        let key = (ir[edge].destination, ir[edge].edge_type.mask());
        exit_groups
            .entry(key)
            .or_default()
            .push(label_indices[&edge]);
    }
    cases.extend(exit_groups.into_values().map(|labels| CaseGroup {
        statement: None,
        labels,
    }));

    for case in &mut cases {
        case.labels.sort_unstable();
    }
    cases.sort_by_key(|case| case.labels[0]);
    sort_fallthrough_cases(ir, head, &mut cases);

    let translated: Vec<_> = cases
        .into_iter()
        .map(|case| {
            let (edges, case_values): (Vec<EdgeId>, Vec<Option<ExprId>>) = case
                .labels
                .into_iter()
                .map(|label| {
                    if label == default_label {
                        (head_successors[0], None)
                    } else {
                        let expr = Expr::new_int_constant(ir, counters, values[label - 1], false);
                        (head_successors[label], Some(expr))
                    }
                })
                .unzip();
            (case.statement, edges, case_values)
        })
        .collect();

    let cases = translated
        .into_iter()
        .map(|(statement, edges, values)| {
            let statement =
                statement.unwrap_or_else(|| create_exit_body(ir, counters, switch, &edges));
            SwitchCase {
                statement,
                edges,
                values,
            }
        })
        .collect();
    let StatementKind::Switch(data) = &mut ir[switch].kind else {
        unreachable!();
    };
    data.cases = cases;
}

fn sort_fallthrough_cases(ir: &Ir, head: StatId, cases: &mut [CaseGroup]) {
    let mut index = 0;
    while index < cases.len() {
        if let Some(stat) = cases[index].statement {
            let predecessor = stat
                .get_neighbours(ir, EdgeType::Regular.mask(), Backward)
                .into_iter()
                .find(|&pred| pred != head);
            if let Some(pred) = predecessor
                && let Some(pred_index) = cases.iter().position(|case| case.statement == Some(pred))
            {
                if pred_index > index {
                    cases[index..=pred_index].rotate_left(1);
                    continue;
                }
                if pred_index + 1 < index {
                    cases[pred_index + 1..=index].rotate_right(1);
                }
            }
        }
        index += 1;
    }
}

fn create_exit_body(
    ir: &mut Ir,
    counters: &mut CounterContainer,
    switch: StatId,
    case_edges: &[EdgeId],
) -> StatId {
    let body = Statement::new_empty_basic_block(ir, counters);
    let sample_edge = &ir[case_edges[0]];
    let exit = StatEdge::new(
        ir,
        sample_edge.edge_type,
        body,
        sample_edge.destination,
        sample_edge.closure,
    );
    body.add_successor(ir, exit);

    for &edge in case_edges {
        edge.change_type(ir, EdgeType::Regular);
        let closure = ir[edge].closure.expect("Switch exit edge has no closure");
        ir[closure].label_edges.shift_remove(&edge);
        edge.change_destination(ir, body);
    }

    let id = ir[body].id;
    ir[switch].stats.add_with_key(body, id);
    ir[body].parent = Some(switch);
    body
}
