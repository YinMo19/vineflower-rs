//! Recover source operations after jumps have been labeled.

mod expression;

use std::io;

use crate::decompiler::exps::{Expr, ExprKind};
use crate::decompiler::ir::{ExprId, Ir, StatId, VarProcessorId};
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
        let if_edge = branch.if_edge.expect("If-else statement has no then edge");
        let successor = ir[empty].first_successor();
        if !ir[empty].exprents.is_some_and(|body| ir[body].is_empty())
            || successor.is_some_and(|edge| ir[edge].explicit)
            || ir[empty].all_predecessors() != [if_edge]
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
        if_edge.remove(ir);
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

/// After slot merging, a plain assignment can become a compound assignment
/// even when its two original variable expressions carried different types.
pub(crate) fn update_assignments(ir: &mut Ir, stat: StatId) -> bool {
    let mut changed = false;
    for index in 0..ir[stat].stats.len() {
        changed |= update_assignments(ir, ir[stat].stats[index]);
    }
    let expressions = ir[stat]
        .exprents
        .map_or_else(|| stat.stat_exprents(ir), |list| ir[list].to_vec());
    for expr in expressions {
        changed |= update_assignment(ir, expr);
    }
    changed
}

fn update_assignment(ir: &mut Ir, expr: ExprId) -> bool {
    let ExprKind::Assignment {
        left,
        right,
        compound: None,
    } = ir[expr].kind
    else {
        return false;
    };
    let Some(target) = Expr::variable(ir, left) else {
        return false;
    };
    let ExprKind::Function { op, operands, .. } = &ir[right].kind else {
        return false;
    };
    if !op.is_arithmetic_binary()
        || Expr::variable(ir, operands[0]).is_none_or(|first| first.index != target.index)
    {
        return false;
    }
    let (op, value) = (*op, operands[1]);
    let ExprKind::Assignment {
        right, compound, ..
    } = &mut ir[expr].kind
    else {
        unreachable!()
    };
    *right = value;
    *compound = Some(op);
    true
}
