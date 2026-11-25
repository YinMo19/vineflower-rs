// SPDX-License-Identifier: Apache-2.0

//! Recover bindings introduced by a successful instanceof check.

mod improve;
pub(crate) mod record;

use std::collections::VecDeque;
use std::io;

use rustc_hash::FxHashSet;

use super::decompose::{finish::condense_sequences, if_helper::merge_all_ifs};
use super::exps::{ConstantValue, Expr, ExprKind, FunctionType};
use super::ir::{ExprId, ExprListId, Ir, StatId};
use super::stats::{IfStatement, StatementKind};
use crate::engine::{Cx, counter_container::CounterContainer};
use crate::structs::StructClass;
use crate::types::VarType;

pub(crate) fn match_instance_of(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    root: StatId,
    class: &StructClass,
) -> io::Result<bool> {
    let cx = &mut *cx.enter_method(counters);
    let changed = Match { cx, counters, root }.visit(root)?;
    if changed {
        condense_sequences(cx, counters, root);
        if merge_all_ifs(cx, counters, root, class) {
            improve::pattern_types(cx, root)?;
        } else {
            condense_sequences(cx, counters, root);
        }
    }
    Ok(changed)
}

struct Match<'a> {
    cx: &'a mut Cx,
    counters: &'a mut CounterContainer,
    root: StatId,
}

#[derive(Clone, Copy)]
struct InstanceOf {
    expr: ExprId,
    source: ExprId,
    target: ExprId,
}

impl Match<'_> {
    fn visit(&mut self, stat: StatId) -> io::Result<bool> {
        let mut changed = false;
        for i in 0..self.cx.ir[stat].stats.len() {
            changed |= self.visit(self.cx.ir[stat].stats[i])?;
        }
        if let StatementKind::If(branch) = self.cx.ir[stat].kind {
            changed |= self.match_if(stat, branch)?;
        }
        Ok(changed)
    }

    fn match_if(&mut self, stat: StatId, branch: IfStatement) -> io::Result<bool> {
        let ir = &self.cx.ir;
        let (_, condition) = header(ir, branch);
        let on_true = last_expr_when(ir, condition, true, true);
        let on_false = last_expr_when(ir, condition, false, true);
        if let Some(test) = on_true
            && self.check_branch(test, stat, self.cx.ir[branch.if_edge.unwrap()].destination)?
        {
            fix_empty_branch(self.cx, self.counters, stat, true);
            return Ok(true);
        }
        if let Some(test) = on_false {
            if let Some(edge) = branch.else_edge {
                if self.check_branch(test, stat, self.cx.ir[edge].destination)? {
                    fix_empty_branch(self.cx, self.counters, stat, false);
                    return Ok(true);
                }
            } else if let &[edge] = self.cx.ir[stat].all_successors() {
                return self.check_branch(test, stat, self.cx.ir[edge].destination);
            }
        }
        Ok(false)
    }

    fn check_branch(&mut self, test: ExprId, stat: StatId, branch: StatId) -> io::Result<bool> {
        let ir = &self.cx.ir;
        let Some(&[source, target]) = operands(ir, test, FunctionType::InstanceOf) else {
            return Ok(false);
        };
        if ir[branch].all_predecessors().len() != 1
            || Expr::usage(ir, source) & Expr::MULTIPLE_USES == 0
        {
            return Ok(false);
        }
        let head = branch.get_basic_head(ir);
        let Some(body) = ir[head].exprents else {
            return Ok(false);
        };
        let Some(&assignment) = ir[body].first() else {
            return Ok(false);
        };
        let ExprKind::Assignment { left, right, .. } = ir[assignment].kind else {
            return Ok(false);
        };
        let test = InstanceOf {
            expr: test,
            source,
            target,
        };
        let mut changed = self.bind_local(test, branch, body, left, right);
        // Matching the local can expose a record extraction at the new head.
        if let Some(&next) = self.cx.ir[body].first()
            && let ExprKind::Assignment { right, .. } = self.cx.ir[next].kind
            && !matches!(self.cx.ir[right].kind, ExprKind::Function { .. })
        {
            changed |= record::match_if(self.cx, self.counters, stat, branch, test.expr, next)?;
        }
        if changed {
            let StatementKind::If(data) = &mut self.cx.ir[stat].kind else {
                unreachable!()
            };
            data.pattern_matched = true;
            self.inline_source(stat, test);
        }
        Ok(changed)
    }

    fn bind_local(
        &mut self,
        test: InstanceOf,
        branch: StatId,
        body: ExprListId,
        left: ExprId,
        right: ExprId,
    ) -> bool {
        let cx = &mut *self.cx;
        let ir = &cx.ir;
        let casted = match &ir[right].kind {
            ExprKind::Function {
                op: FunctionType::Cast,
                operands,
                ..
            } => operands[0],
            ExprKind::Variable(_) => right,
            _ => return false,
        };
        let Some(local) = Expr::variable(ir, left) else {
            return false;
        };
        if !Expr::equals(cx, test.source, casted)
            || Expr::expr_type(cx, test.target) != local.expr_type(cx)
            || assigned_before(ir, branch, local.index)
        {
            return false;
        }
        let ty = local.inferred_expr_type(cx);
        let ir = &mut cx.ir;
        let target = if ty.is_generic() {
            Expr::new(
                ir,
                self.counters,
                Expr::constant(ty, ConstantValue::Null, false),
                ir[test.target].bytecode.clone(),
            )
        } else {
            test.target
        };
        let ExprKind::Function { operands, .. } = &mut ir[test.expr].kind else {
            unreachable!()
        };
        operands[1] = target;
        operands.push(left);
        ir[body].remove(0);
        true
    }

    fn inline_source(&mut self, stat: StatId, test: InstanceOf) {
        let source = test.source;
        let ir = &self.cx.ir;
        let head = stat.get_basic_head(ir);
        let Some(body) = ir[head].exprents else {
            return;
        };
        let Some(&last) = ir[body].last() else { return };
        let ExprKind::Assignment { left, right, .. } = ir[last].kind else {
            return;
        };
        if Expr::variable(ir, source).is_some()
            && operands(ir, right, FunctionType::Cast).is_none()
            && Expr::equals(self.cx, source, left)
            && !Expr::is_var_referenced_in_stat(ir, source, self.root, &[left])
        {
            let ir = &mut self.cx.ir;
            let ExprKind::Function { operands, .. } = &mut ir[test.expr].kind else {
                unreachable!()
            };
            operands[0] = right;
            ir[body].pop();
        }
    }
}

fn operands(ir: &Ir, expr: ExprId, expected: FunctionType) -> Option<&[ExprId]> {
    match &ir[expr].kind {
        ExprKind::Function { op, operands, .. } if *op == expected => Some(operands),
        _ => None,
    }
}

fn header(ir: &Ir, branch: IfStatement) -> (ExprId, ExprId) {
    let head = ir[branch.head_exprents.unwrap()][0];
    let ExprKind::If { condition } = ir[head].kind else {
        unreachable!("Expected IfExprent")
    };
    (head, condition)
}

/// The last subexpression guaranteed to have executed for this truth value.
pub(crate) fn last_expr_when(
    ir: &Ir,
    mut expr: ExprId,
    mut if_true: bool,
    only_if_true: bool,
) -> Option<ExprId> {
    use FunctionType::*;
    while let ExprKind::Function { op, operands, .. } = &ir[expr].kind {
        match op {
            BoolAnd if if_true => expr = operands[1],
            BoolOr if !if_true => expr = operands[1],
            BoolNot => {
                expr = operands[0];
                if_true = !if_true;
            }
            Eq | Ne => {
                let ExprKind::Constant {
                    value: ConstantValue::Integer(value),
                    var_type,
                    ..
                } = &ir[operands[1]].kind
                else {
                    break;
                };
                if *var_type != VarType::VARTYPE_BOOLEAN {
                    break;
                }
                if_true ^= (*op == Eq) == (*value == 0);
                expr = operands[0];
            }
            _ => break,
        }
    }
    (if_true || !only_if_true).then_some(expr)
}

fn assigned_before(ir: &Ir, branch: StatId, slot: i32) -> bool {
    let mut pending = VecDeque::from([branch]);
    let mut seen = FxHashSet::default();
    while let Some(stat) = pending.pop_front() {
        if !seen.insert(stat) {
            continue;
        }
        if let Some(parent) = ir[stat].parent
            && (matches!(ir[parent].kind, StatementKind::If(_))
                || matches!(ir[stat].kind, StatementKind::If(_)))
        {
            pending.push_back(parent);
        }
        for &edge in ir[stat].all_predecessors() {
            let source = ir[edge].source;
            pending.push_back(source);
            if source == branch || branch.contains_statement_strict(ir, source) {
                continue;
            }
            let Some(list) = ir[source].exprents else {
                continue;
            };
            if ir[list].iter().any(|&expr| match ir[expr].kind {
                ExprKind::Assignment { left, .. } => {
                    Expr::variable(ir, left).is_some_and(|var| var.index == slot)
                }
                _ => false,
            }) {
                return true;
            }
        }
    }
    false
}

/// The two IfStatement invariant repairs share the removal of the empty basic
/// block and its exit. When the true arm is removed the surviving arm is negated.
fn fix_empty_branch(cx: &mut Cx, counters: &mut CounterContainer, stat: StatId, then_arm: bool) {
    let ir = &mut cx.ir;
    let StatementKind::If(branch) = ir[stat].kind else {
        unreachable!()
    };
    let empty = if then_arm {
        branch.if_stat
    } else {
        branch.else_stat
    };
    let Some(empty) = empty.filter(|_| branch.has_else) else {
        return;
    };
    if !matches!(ir[empty].kind, StatementKind::BasicBlock { .. })
        || !ir[empty].exprents.is_some_and(|list| ir[list].is_empty())
    {
        return;
    }

    let id = ir[empty].id;
    ir[stat].stats.remove_with_key(&id);
    let discarded = if then_arm {
        branch.if_edge
    } else {
        branch.else_edge
    };
    discarded.unwrap().remove(ir);
    let successor = ir[empty]
        .first_successor()
        .expect("Empty conditional branch has no exit");
    if ir[stat].first_successor().is_none() {
        successor.change_source(ir, stat);
    } else {
        successor.remove(ir);
    }
    let StatementKind::If(data) = &mut ir[stat].kind else {
        unreachable!()
    };
    data.has_else = false;
    data.else_stat = None;
    data.else_edge = None;
    if then_arm {
        data.if_stat = branch.else_stat;
        data.if_edge = branch.else_edge;
        data.negated = !data.negated;
        let slot = branch.head_exprents.unwrap();
        let copy = Expr::copy(cx, counters, cx.ir[slot][0]);
        Expr::negate_if(&mut cx.ir, counters, copy);
        cx.ir[slot][0] = copy;
    }
}
