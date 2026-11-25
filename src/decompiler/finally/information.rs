// Copyright 2000-2024 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Track uses of the exception captured by a catch-all to identify its rethrows.

use std::{collections::VecDeque, io};

use indexmap::IndexMap;
use rustc_hash::FxHashSet;

use super::{FinallyInfo, HandlerKind, basic_head};
use crate::code::code_constants::{OPC_ASTORE, OPC_POP};
use crate::decompiler::exps::{ExitType, Expr, ExprKind};
use crate::decompiler::flow::{DirectEdgeType, DirectGraph, DirectId};
use crate::decompiler::ir::{ExprId, Ir, StatId};
use crate::decompiler::sforms::split_ssa;
use crate::decompiler::stats::{STATEDGE_DIRECT_ALL, StatementKind, stat_edge::EdgeType};
use crate::decompiler::vars::var_version_pair::VarVersionPair;
use crate::engine::Cx;
use crate::structs::StructMethod;

pub(super) fn inspect(
    cx: &mut Cx,
    root: StatId,
    catch_all: StatId,
    method: &StructMethod,
) -> io::Result<Option<FinallyInfo>> {
    let StatementKind::CatchAll {
        handler: Some(handler),
        ..
    } = cx.ir[catch_all].kind
    else {
        unreachable!()
    };
    let first = handler.get_basic_head(&cx.ir);
    let first_block = basic_head(&cx.ir, first);
    let seq = &cx.ir[first_block].seq;
    if seq.is_empty() {
        return Ok(None);
    }
    let instr = seq.get_instr(0);
    let mut kind = match instr.opcode {
        OPC_POP => HandlerKind::Pop,
        OPC_ASTORE => HandlerKind::Store,
        _ => HandlerKind::Stack,
    };
    let exception_offset = instr.start_offset;

    // SSA writes versions into the expressions already shared by the direct nodes.
    let graph = split_ssa(&mut cx.ir, root, method).graph;
    let ir = &cx.ir;
    let exception = ir[first]
        .exprents
        .and_then(|list| ir[list].get(usize::from(kind == HandlerKind::Store)))
        .and_then(|&expr| match ir[expr].kind {
            ExprKind::Assignment { left, .. } => pair(ir, left),
            _ => None,
        })
        .ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                "missing exception variable at finally handler entry",
            )
        })?;

    let mut last = IndexMap::new();
    let mut visited = FxHashSet::default();
    let mut pending = VecDeque::from([graph.first]);
    while let Some(id) = pending.pop_front() {
        let node = &graph[id];
        if !visited.insert(&node.id) {
            continue;
        }
        let start = if node.block != Some(first) {
            0
        } else if kind == HandlerKind::Store {
            2
        } else {
            1
        };
        let Some(true_exit) = classify_exit(cx, &graph, id, kind, exception, start) else {
            return Ok(None);
        };
        let block_stat = node.block.or_else(|| {
            let [pred] = node.predecessors(DirectEdgeType::Regular) else {
                return None;
            };
            graph[*pred].block
        });
        if let Some(block_stat) = block_stat
            && contains(ir, handler, block_stat)
            && block_stat
                .get_successor_edges(ir, STATEDGE_DIRECT_ALL)
                .iter()
                .any(|&edge| {
                    ir[edge].edge_type != EdgeType::Regular
                        && !contains(ir, handler, ir[edge].destination)
                })
        {
            *last.entry(basic_head(ir, block_stat)).or_insert(false) |= true_exit;
        }
        pending.extend(node.successors(DirectEdgeType::Regular));
    }
    if matches!(ir[handler].kind, StatementKind::BasicBlock { .. }) {
        let is_exit = last.contains_key(&first_block);
        let length = ir[first_block].seq.length();
        if match kind {
            HandlerKind::Stack => is_exit && length == 1,
            HandlerKind::Pop => length == 1,
            HandlerKind::Store => length == if is_exit { 3 } else { 1 },
            HandlerKind::Empty => unreachable!(),
        } {
            kind = HandlerKind::Empty;
        }
    }
    Ok(Some(FinallyInfo {
        first_code: kind,
        exception_offset,
        last,
    }))
}

/// Some(true) reports the original exception being rethrown. A different use
/// of that exception prevents this catch-all from being recovered as a finally.
fn classify_exit(
    cx: &Cx,
    graph: &DirectGraph,
    id: DirectId,
    kind: HandlerKind,
    exception: VarVersionPair,
    start: usize,
) -> Option<bool> {
    if kind == HandlerKind::Pop {
        return Some(true);
    }
    let ir = &cx.ir;
    let node = &graph[id];
    let exprs = &ir[node.exprents];
    let mut rethrows = false;
    for (index, &expr) in exprs.iter().enumerate().skip(start) {
        match kind {
            HandlerKind::Stack => {
                if Expr::children(ir, expr)
                    .chain([expr])
                    .any(|e| pair(ir, e) == Some(exception))
                {
                    thrown_variable(ir, expr)?;
                    rethrows = true;
                }
            }
            HandlerKind::Store => {
                if let ExprKind::Assignment { left, right, .. } = ir[expr].kind
                    && pair(ir, right) == Some(exception)
                {
                    let next = exprs.get(index + 1).copied().or_else(|| {
                        let [next] = node.successors(DirectEdgeType::Regular) else {
                            return None;
                        };
                        ir[graph[*next].exprents].first().copied()
                    })?;
                    let thrown = thrown_variable(ir, next)?;
                    if pair(ir, left) != pair(ir, thrown)
                        || Expr::expr_type(cx, left) != Expr::expr_type(cx, thrown)
                    {
                        return None;
                    }
                    rethrows = true;
                }
            }
            HandlerKind::Pop | HandlerKind::Empty => unreachable!(),
        }
    }
    Some(rethrows)
}

fn thrown_variable(ir: &Ir, expr: ExprId) -> Option<ExprId> {
    match ir[expr].kind {
        ExprKind::Exit {
            kind: ExitType::Throw,
            value: Some(value),
            ..
        } if matches!(ir[value].kind, ExprKind::Variable(_)) => Some(value),
        _ => None,
    }
}

fn pair(ir: &Ir, expr: ExprId) -> Option<VarVersionPair> {
    match &ir[expr].kind {
        ExprKind::Variable(var) => Some(VarVersionPair::new(var.index, var.version)),
        _ => None,
    }
}

fn contains(ir: &Ir, parent: StatId, stat: StatId) -> bool {
    parent == stat || parent.contains_statement_strict(ir, stat)
}
