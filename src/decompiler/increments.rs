// Copyright 2000-2017 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Recover prefix increments and move them into conditions as `PPandMMHelper` does.

use crate::decompiler::exps::{Expr, ExprKind, FunctionType, delta_by_one, increment};
use crate::decompiler::flow::{DirectGraph, flatten::build_direct_graph};
use crate::decompiler::ir::{ExprId, Ir, StatId, VarProcessorId};
use crate::decompiler::stats::StatementKind;
use crate::decompiler::vars::var_version_pair::VarVersionPair;
use crate::engine::{Cx, counter_container::CounterContainer};

pub(crate) fn find(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    root: StatId,
    owner: VarProcessorId,
) -> bool {
    let graph = build_direct_graph(&mut cx.ir, root);
    let mut finder = Finder {
        cx,
        counters,
        graph: &graph,
        owner,
    };
    let mut changed = false;
    for node in graph.regular_breadth_first() {
        let list = graph[node].exprents;
        let mut index = 0;
        while index < finder.cx.ir[list].len() {
            let expr = finder.cx.ir[list][index];
            let (replacement, updated) = finder.process_expr(expr);
            changed |= updated;
            if let Some(replacement) = replacement {
                finder.cx.ir[list][index] = replacement;
            } else {
                index += 1;
            }
        }
    }
    changed
}

struct Finder<'a> {
    cx: &'a mut Cx,
    counters: &'a mut CounterContainer,
    graph: &'a DirectGraph,
    owner: VarProcessorId,
}

impl Finder<'_> {
    fn process_expr(&mut self, expr: ExprId) -> (Option<ExprId>, bool) {
        let mut changed = false;
        loop {
            let mut replaced = false;
            let children: Vec<_> = Expr::children(&self.cx.ir, expr).collect();
            for child in children {
                let (replacement, nested) = self.process_expr(child);
                changed |= nested;
                if let Some(replacement) = replacement {
                    let offsets = self.cx.ir[child].bytecode.clone();
                    Expr::replace(&mut self.cx.ir, expr, child, replacement);
                    Expr::add_offsets(&mut self.cx.ir, replacement, offsets.as_ref());
                    replaced = true;
                    break;
                }
            }
            if !replaced {
                break;
            }
        }
        let replacement = self.prefix(expr);
        (replacement, changed || replacement.is_some())
    }

    fn prefix(&mut self, expr: ExprId) -> Option<ExprId> {
        let ir = &self.cx.ir;
        let ExprKind::Assignment { left, right, .. } = ir[expr].kind else {
            return None;
        };
        let ExprKind::Function { op, operands, .. } = &ir[right].kind else {
            return None;
        };
        // Numeric conversions are the FunctionType entries with a castType.
        let midlayer = matches!(
            op,
            FunctionType::I2l
                | FunctionType::I2f
                | FunctionType::I2d
                | FunctionType::L2i
                | FunctionType::L2f
                | FunctionType::L2d
                | FunctionType::F2i
                | FunctionType::F2l
                | FunctionType::F2d
                | FunctionType::D2i
                | FunctionType::D2l
                | FunctionType::D2f
                | FunctionType::I2b
                | FunctionType::I2c
                | FunctionType::I2s
        )
        .then(|| Expr::expr_type(self.cx, right));
        let arithmetic = if midlayer.is_some() {
            operands[0]
        } else {
            right
        };
        let (operand, add) = delta_by_one(ir, arithmetic)?;
        let ty = Expr::expr_type(self.cx, left);
        if !same_target(self.cx, self.owner, left, operand)
            || midlayer.is_some_and(|cast| cast != ty)
        {
            return None;
        }
        let op = if add {
            FunctionType::Ppi
        } else {
            FunctionType::Mmi
        };
        let replacement = increment(self.cx, self.counters, arithmetic, op, operand, ty);
        if !Expr::equals(self.cx, left, operand) {
            let old = variable_pair(&self.cx.ir, left).unwrap();
            let new = variable_pair(&self.cx.ir, operand).unwrap();
            for id in self.graph.deep_exprents(&self.cx.ir) {
                if let ExprKind::Variable(var) = &mut self.cx.ir[id].kind
                    && old.is(var.index, var.version)
                {
                    var.index = new.var;
                    var.version = new.version;
                }
            }
        }
        Some(replacement)
    }
}

fn same_target(cx: &Cx, owner: VarProcessorId, left: ExprId, operand: ExprId) -> bool {
    if left == operand {
        return true;
    }
    let Some(left_var) = variable_pair(&cx.ir, left) else {
        return Expr::equals(cx, left, operand);
    };
    let Some(right_var) = variable_pair(&cx.ir, operand) else {
        return false;
    };
    let original = &cx.ir[owner].original;
    // Java compares the Integer objects returned by getVarOriginalIndex.
    // Equal values outside the default Integer cache are boxed independently.
    match (original.get(&left_var.var), original.get(&right_var.var)) {
        (None, None) => true,
        (Some(left), Some(right)) => left.var == right.var && (-128..=127).contains(&left.var),
        _ => false,
    }
}

fn variable_pair(ir: &Ir, expr: ExprId) -> Option<VarVersionPair> {
    let ExprKind::Variable(var) = &ir[expr].kind else {
        return None;
    };
    Some(VarVersionPair::new(var.index, var.version))
}

/// The caller condenses sequences with the method counters when this changes the tree.
pub(crate) fn inline_in_conditions(cx: &mut Cx, stat: StatId) -> bool {
    let mut changed = false;
    for index in 0..cx.ir[stat].stats.len() {
        let child = cx.ir[stat].stats[index];
        changed |= inline_in_conditions(cx, child);
    }
    // Java returns false immediately for a rejected condition in this frame.
    inline_condition(cx, stat).unwrap_or(changed)
}

fn inline_condition(cx: &mut Cx, stat: StatId) -> Option<bool> {
    let ir = &cx.ir;
    let list = ir[stat].exprents?;
    let &increment = ir[list].last()?;
    let parent = ir[stat].parent?;
    let StatementKind::If(branch) = ir[parent].kind else {
        return None;
    };
    if ir[parent].first != Some(stat) {
        return None;
    }
    let ExprKind::Function {
        op: FunctionType::Ppi | FunctionType::Mmi,
        operands,
        ..
    } = &ir[increment].kind
    else {
        return None;
    };
    let index = variable_pair(ir, operands[0])?.var;
    let &head = ir[branch.head_exprents?].first()?;
    let ExprKind::If { mut condition } = ir[head].kind else {
        return None;
    };
    if !matches!(ir[condition].kind, ExprKind::Function { .. }) {
        return None;
    }
    while let ExprKind::Function {
        op: FunctionType::BoolNot,
        operands,
        ..
    } = &ir[condition].kind
    {
        let inner = operands[0];
        if !matches!(ir[inner].kind, ExprKind::Function { .. }) {
            break;
        }
        condition = inner;
    }

    let mut old = None;
    for child in Expr::all_exprents(ir, condition, true, false) {
        match &ir[child].kind {
            ExprKind::Variable(var) if var.index == index && old.is_some() => return Some(false),
            ExprKind::Variable(var) if var.index == index => old = Some(child),
            ExprKind::Function {
                op: FunctionType::BoolAnd | FunctionType::BoolOr,
                ..
            } => {
                return Some(false);
            }
            _ => {}
        }
    }
    let old = old?;
    let mut pending = vec![condition];
    while let Some(expr) = pending.pop() {
        let found = Expr::children(&cx.ir, expr).any(|child| {
            if child == old {
                true
            } else {
                pending.push(child);
                false
            }
        });
        if found {
            let offsets = cx.ir[old].bytecode.clone();
            Expr::replace(&mut cx.ir, expr, old, increment);
            Expr::add_offsets(&mut cx.ir, increment, offsets.as_ref());
            break;
        }
    }
    // List.remove(Object) removes the first structurally equal expression.
    let index = cx.ir[list]
        .iter()
        .position(|&candidate| Expr::equals(cx, increment, candidate))
        .unwrap();
    cx.ir[list].remove(index);
    let StatementKind::If(branch) = &mut cx.ir[parent].kind else {
        unreachable!()
    };
    branch.has_ppmm = true;
    Some(true)
}
