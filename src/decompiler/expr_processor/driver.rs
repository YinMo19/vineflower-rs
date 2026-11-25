// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! The graph traversal in ExprProcessor.processStatement. A node inherits the
//! first incoming stack discovered, and every entry on that stack is a fresh
//! copy. Expression IDs make both discovery order and copy order observable.

use std::{io, sync::Arc};

use arcstr::ArcStr;
use rustc_hash::{FxHashMap, FxHashSet};

use super::{ExpressionData, block};
use crate::decompiler::exps::{Expr, ExprKind, FunctionType, STACK_BASE, SwitchCaseValues};
use crate::decompiler::flow::{DirectEdgeType, DirectGraph, flatten::build_direct_graph};
use crate::decompiler::ir::{ExprId, Ir, StatId};
use crate::decompiler::stats::StatementKind;
use crate::engine::{Cx, counter_container::CounterContainer};
use crate::structs::{StructClass, StructMethod};
use crate::types::MethodDescriptor;

pub fn process_statement(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    root: StatId,
    class: &StructClass,
    method: &StructMethod,
    descriptor: &Arc<MethodDescriptor>,
) -> io::Result<()> {
    let graph = build_direct_graph(&mut cx.ir, root);
    let mut catch_variables = FxHashMap::default();
    collect_catch_variables(&cx.ir, root, &graph, &mut catch_variables)?;

    // DirectNode.equals compares the generated name and kind. The name
    // includes the kind's suffix, even for separately allocated nodes.
    let mut discovered = FxHashSet::default();
    discovered.insert(&graph[graph.first].id);
    let mut pending = vec![(graph.first, Vec::new())];
    while let Some((node, incoming)) = pending.pop() {
        let mut data = match catch_variables.get(&graph[node].id) {
            Some(&var) => catch_entry(cx, counters, var),
            None => ExpressionData {
                stack: incoming,
                expressions: Vec::new(),
            },
        };
        if let Some(stat) = graph[node].block {
            block::process_block(cx, counters, stat, &mut data, class, method, descriptor)?;
            cx.ir[stat].exprents = Some(cx.ir.new_list(data.expressions));
        }
        for &next in graph[node].successors(DirectEdgeType::Regular) {
            if discovered.insert(&graph[next].id) {
                let stack = data
                    .stack
                    .iter()
                    .map(|&id| Expr::copy(cx, counters, id))
                    .collect();
                pending.push((next, stack));
            }
        }
    }
    init_headers(cx, counters, root)
}

fn collect_catch_variables(
    ir: &Ir,
    stat: StatId,
    graph: &DirectGraph,
    variables: &mut FxHashMap<ArcStr, ExprId>,
) -> io::Result<()> {
    match &ir[stat].kind {
        StatementKind::Catch { vars, .. }
        | StatementKind::CatchAll {
            is_finally: false,
            vars,
            ..
        } => {
            for (&handler, &variable) in ir[stat].stats[1..].iter().zip(vars) {
                let node = graph.direct_node(handler).ok_or_else(|| {
                    io::Error::new(
                        io::ErrorKind::InvalidData,
                        format!(
                            "missing direct node for exception handler {}",
                            ir[handler].id
                        ),
                    )
                })?;
                variables.insert(graph[node].id.clone(), variable);
            }
        }
        _ => {}
    }
    for &child in &ir[stat].stats {
        collect_catch_variables(ir, child, graph, variables)?;
    }
    Ok(())
}

fn catch_entry(cx: &mut Cx, counters: &mut CounterContainer, catch: ExprId) -> ExpressionData {
    let ty = Expr::expr_type(cx, catch);
    let temp = Expr::new_stack_variable(&mut cx.ir, counters, STACK_BASE, ty);
    let catch = Expr::copy(cx, counters, catch);
    let ExprKind::Variable(var) = &mut cx.ir[catch].kind else {
        unreachable!()
    };
    var.catch_temp = true;
    let assignment = Expr::new(
        &mut cx.ir,
        counters,
        ExprKind::Assignment {
            left: temp,
            right: catch,
            compound: None,
        },
        None,
    );
    ExpressionData {
        expressions: vec![assignment],
        stack: vec![Expr::copy(cx, counters, temp)],
    }
}

fn init_headers(cx: &mut Cx, counters: &mut CounterContainer, root: StatId) -> io::Result<()> {
    let mut pending = vec![root];
    while let Some(stat) = pending.pop() {
        initialize_header(cx, counters, stat)?;
        pending.extend(cx.ir[stat].stats.iter().rev().copied());
    }
    Ok(())
}

fn initialize_header(cx: &mut Cx, counters: &mut CounterContainer, stat: StatId) -> io::Result<()> {
    let head = match &cx.ir[stat].kind {
        StatementKind::If(branch) => {
            let negated = branch.negated;
            let head = take_header(&mut cx.ir, stat)?;
            let ExprKind::If { .. } = cx.ir[head].kind else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "expected an if expression",
                ));
            };
            if negated {
                negate_if_copy(cx, counters, head)
            } else {
                head
            }
        }
        StatementKind::Switch(_) => {
            let head = take_header(&mut cx.ir, stat)?;
            let ExprKind::SwitchHead { case_values, .. } = &mut cx.ir[head].kind else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "expected a switch expression",
                ));
            };
            *case_values = Some(SwitchCaseValues::Statement(stat));
            head
        }
        StatementKind::Synchronized { .. } => take_header(&mut cx.ir, stat)?,
        _ => return Ok(()),
    };

    // Preserve the list identity when finally analysis lifts the tree again.
    let slot = match &mut cx.ir.stats[stat].kind {
        StatementKind::If(branch) => &mut branch.head_exprents,
        StatementKind::Switch(switch) => &mut switch.head_exprents,
        StatementKind::Synchronized { head_exprents, .. } => head_exprents,
        _ => unreachable!(),
    };
    match *slot {
        Some(list) => cx.ir.lists[list][0] = head,
        None => *slot = Some(cx.ir.lists.push(vec![head])),
    }
    Ok(())
}

fn take_header(ir: &mut Ir, stat: StatId) -> io::Result<ExprId> {
    ir[stat]
        .first
        .and_then(|first| ir[first].exprents)
        .and_then(|list| ir[list].pop())
        .ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                format!("missing header expression for statement {}", ir[stat].id),
            )
        })
}

fn negate_if_copy(cx: &mut Cx, counters: &mut CounterContainer, head: ExprId) -> ExprId {
    let copy = Expr::copy(cx, counters, head);
    let ExprKind::If { condition } = cx.ir[copy].kind else {
        unreachable!()
    };
    let bytecode = cx.ir[condition].bytecode.clone();
    let negation = ExprKind::Function {
        op: FunctionType::BoolNot,
        operands: vec![condition],
    };
    let condition = Expr::new(&mut cx.ir, counters, negation, bytecode);
    cx.ir[copy].kind = ExprKind::If { condition };
    copy
}
