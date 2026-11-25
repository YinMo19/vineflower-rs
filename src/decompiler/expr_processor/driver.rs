// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! The graph traversal in ExprProcessor.processStatement. A node inherits the
//! first incoming stack discovered, and every entry on that stack is a fresh
//! copy. Expression IDs make both discovery order and copy order observable.

use std::{io, sync::Arc};

use arcstr::ArcStr;
use rustc_hash::{FxHashMap, FxHashSet};

use super::{ExpressionData, block};
use crate::decompiler::exps::Variable;
use crate::decompiler::exps::{Expr, ExprKind, STACK_BASE, SwitchCaseValues};
use crate::decompiler::flow::{DirectEdgeType, DirectGraph, flatten::build_direct_graph};
use crate::decompiler::ir::{ExprId, Ir, StatId, VarProcessorId};
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
    owner: VarProcessorId,
) -> io::Result<()> {
    let cx = &mut *cx.enter_method(counters);
    let graph = build_direct_graph(&mut cx.ir, root);
    let mut catch_variables = FxHashMap::default();
    collect_catch_variables(&mut cx.ir, root, &graph, owner, &mut catch_variables)?;

    // DirectNode.equals compares the generated name and kind. The name
    // includes the kind's suffix, even for separately allocated nodes.
    let mut discovered = FxHashSet::default();
    discovered.insert(&graph[graph.first].id);
    let mut pending = vec![(graph.first, Vec::new())];
    while let Some((node, incoming)) = pending.pop() {
        let mut data = match catch_variables.get(&graph[node].id) {
            Some(&var) => catch_entry(cx, counters, var, owner),
            None => ExpressionData {
                variables: owner,
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
    ir: &mut Ir,
    stat: StatId,
    graph: &DirectGraph,
    owner: VarProcessorId,
    variables: &mut FxHashMap<ArcStr, ExprId>,
) -> io::Result<()> {
    let statement = &ir.stats[stat];
    if let StatementKind::Catch { vars, .. } | StatementKind::CatchAll { vars, .. } =
        &statement.kind
    {
        // These implicit variables are created by statement recognition, before
        // the expression processor binds the method's locals to its type table.
        for &variable in vars {
            let ExprKind::Variable(var) = &mut ir.exprs[variable].kind else {
                unreachable!()
            };
            var.processor = Some(owner);
        }
        if !matches!(
            statement.kind,
            StatementKind::CatchAll {
                is_finally: true,
                ..
            }
        ) {
            for (&handler, &variable) in statement.stats[1..].iter().zip(vars) {
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
    }
    for index in 0..ir[stat].stats.len() {
        let child = ir[stat].stats[index];
        collect_catch_variables(ir, child, graph, owner, variables)?;
    }
    Ok(())
}

fn catch_entry(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    catch: ExprId,
    owner: VarProcessorId,
) -> ExpressionData {
    let ty = Expr::expr_type(cx, catch);
    let temp = Variable::in_method(STACK_BASE, ty, owner).push_stack(&mut cx.ir, counters);
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
        variables: owner,
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
                let copy = Expr::copy(cx, counters, head);
                Expr::negate_if(&mut cx.ir, counters, copy);
                copy
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
