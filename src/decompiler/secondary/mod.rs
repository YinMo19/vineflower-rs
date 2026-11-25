// Copyright 2000-2020 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Recover source operations after jumps have been labeled.

mod expression;

use std::io;

use crate::decompiler::exps::Expr;
use crate::decompiler::ir::{StatId, VarProcessorId};
use crate::decompiler::stats::StatementKind;
use crate::engine::{Cx, counter_container::CounterContainer};

pub(crate) fn identify(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    root: StatId,
    owner: VarProcessorId,
    force_ternary: bool,
) -> io::Result<bool> {
    let mut method = cx.enter_method(counters);
    Rewrite {
        cx: &mut method,
        counters,
        root,
        owner,
        force_ternary,
    }
    .identify_statement(root)
}

struct Rewrite<'a> {
    cx: &'a mut Cx,
    counters: &'a mut CounterContainer,
    root: StatId,
    owner: VarProcessorId,
    force_ternary: bool,
}

impl Rewrite<'_> {
    fn identify_statement(&mut self, stat: StatId) -> io::Result<bool> {
        if self.cx.ir[stat].exprents.is_none() && self.move_else_to_empty_then(stat) {
            return Ok(true);
        }

        let mut changed = false;
        loop {
            let mut replaced = false;
            for index in 0..self.cx.ir[stat].stats.len() {
                let child = self.cx.ir[stat].stats[index];
                if self.identify_statement(child)? {
                    replaced = true;
                    break;
                }
            }
            // A changed child still allows one expression rewrite at this level.
            let body = self.cx.ir[stat].exprents;
            let exprs = body.map_or_else(
                || stat.stat_exprents(&self.cx.ir),
                |list| self.cx.ir[list].to_vec(),
            );
            for (index, expr) in exprs.into_iter().enumerate() {
                if let Some(new) = self.identify_expression(expr, true)? {
                    if let Some(body) = body {
                        self.cx.ir[body][index] = new;
                    } else {
                        stat.replace_header(self.cx, expr, new);
                    }
                    replaced = true;
                    break;
                }
            }
            if !replaced {
                return Ok(changed);
            }
            changed = true;
        }
    }

    fn move_else_to_empty_then(&mut self, stat: StatId) -> bool {
        let ir = &mut self.cx.ir;
        let StatementKind::If(branch) = ir[stat].kind else {
            return false;
        };
        let Some(empty) = branch.if_stat.filter(|_| branch.has_else) else {
            return false;
        };
        let successor = ir[empty].first_successor();
        if !ir[empty].exprents.is_some_and(|body| ir[body].is_empty())
            || successor.is_some_and(|edge| ir[edge].explicit)
        {
            return false;
        }

        let id = ir[empty].id;
        ir[stat].stats.remove_with_key(&id);
        if ir[stat].first_successor().is_none()
            && let Some(edge) = successor
        {
            edge.remove(ir);
            ir[edge].source = stat;
            if ir[edge].closure.is_some() {
                ir[stat].parent.unwrap().add_labeled_edge(ir, edge);
            }
            stat.add_successor(ir, edge);
        }
        branch.if_edge.unwrap().remove(ir);
        let StatementKind::If(branch) = &mut ir[stat].kind else {
            unreachable!()
        };
        branch.has_else = false;
        branch.if_stat = branch.else_stat.take();
        branch.if_edge = branch.else_edge.take();
        branch.negated = !branch.negated;
        let head = branch.head_exprents.unwrap();
        let copy = Expr::copy(self.cx, self.counters, self.cx.ir[head][0]);
        Expr::negate_if(&mut self.cx.ir, self.counters, copy);
        self.cx.ir[head][0] = copy;
        true
    }
}
