//! Recover the close calls on normal exits and in a suppressed-exception handler.

use indexmap::IndexSet;

use super::{Initializer, catches_throwable, close_receiver, resource_list};
use crate::decompiler::decompose::finish::destroy_and_flatten_statement;
use crate::decompiler::exps::{ExitType, Expr, ExprKind, FunctionType};
use crate::decompiler::ir::{ExprId, Ir, StatId};
use crate::decompiler::stats::{IfStatement, Statement, StatementKind, stat_edge::EdgeType};
use crate::engine::{Cx, counter_container::CounterContainer};
use crate::types::VarType;

#[derive(Clone, Copy)]
struct Close {
    var: ExprId,
    nullable: bool,
}

pub(super) fn recover(cx: &mut Cx, counters: &mut CounterContainer, stat: StatId) -> bool {
    let ir = &cx.ir;
    let Some(close) = handler_close(cx, stat) else {
        return false;
    };
    let exits = exit_points(ir, stat);
    if exits.is_empty() {
        return false;
    }
    let incoming = std::iter::successors(Some(stat), |&s| ir[s].parent).find_map(|s| {
        s.get_predecessor_edges(ir, EdgeType::Regular.mask())
            .first()
            .copied()
    });
    let Some(init) = incoming.map(|edge| ir[edge].source) else {
        return false;
    };
    if !matches!(ir[init].kind, StatementKind::BasicBlock { .. }) {
        return false;
    }
    let Some(initializer) = Initializer::find(ir, init, close.var) else {
        return false;
    };
    if !exits.iter().all(|&dest| close.matches_exit(cx, dest)) {
        return false;
    }
    for dest in exits {
        close.remove_exit(cx, counters, dest);
    }
    initializer.remove(cx);
    let def = initializer.expr;
    let resources = resource_list(&mut cx.ir, stat);
    cx.ir[resources].insert(0, def);
    let handler = cx.ir[stat].stats[1];
    destroy_and_flatten_statement(cx, counters, stat, handler);
    cx.ir[stat].stats.remove(1);

    let (left, right) = cx.ir[def].as_assignment().unwrap();
    if matches!(
        cx.ir[right].kind,
        ExprKind::Variable(_) | ExprKind::Field(_)
    ) && !Expr::is_var_referenced_in_stat(&cx.ir, left, stat, &[])
    {
        cx.ir[resources][0] = right;
    }
    for dest in exit_points(&cx.ir, stat) {
        inline_return(cx, counters, stat, dest);
    }
    true
}

fn handler_close(cx: &Cx, stat: StatId) -> Option<Close> {
    let ir = &cx.ir;
    let &handler = ir[stat].stats.get(1)?;
    if !catches_throwable(cx, stat, 0) || !matches!(ir[handler].kind, StatementKind::Sequence) {
        return None;
    }
    let &first = ir[handler].stats.first()?;
    let (catch, checked) = match ir[first].kind {
        StatementKind::Catch { .. } => (first, None),
        StatementKind::If(branch) => {
            let (_, source, target) = condition_operands(ir, branch)?;
            let checked = Expr::variable(ir, source)?.pair();
            if Expr::expr_type(cx, target) != VarType::VARTYPE_NULL {
                return None;
            }
            (branch.if_stat?, Some(checked))
        }
        _ => return None,
    };
    let &body = ir[catch].stats.first()?;
    if !catches_throwable(cx, catch, 0)
        || !matches!(ir[body].kind, StatementKind::BasicBlock { .. })
    {
        return None;
    }
    let &call = ir[ir[body].exprents?].first()?;
    let var = close_receiver(cx, call)?;
    let pair = Expr::variable(ir, var)?.pair();
    checked
        .is_none_or(|candidate| candidate == pair)
        .then_some(Close {
            var,
            nullable: checked.is_some(),
        })
}

fn condition_operands(ir: &Ir, branch: IfStatement) -> Option<(FunctionType, ExprId, ExprId)> {
    let head = ir[branch.head_exprents?][0];
    let ExprKind::If { mut condition } = ir[head].kind else {
        return None;
    };
    while let ExprKind::Function { op, operands, .. } = &ir[condition].kind {
        if *op == FunctionType::BoolNot && matches!(ir[operands[0]].kind, ExprKind::Function { .. })
        {
            condition = operands[0];
        } else {
            return Some((*op, *operands.first()?, *operands.get(1)?));
        }
    }
    None
}

fn exit_points(ir: &Ir, stat: StatId) -> IndexSet<StatId> {
    ir[stat]
        .first
        .unwrap()
        .edges_leaving(ir, stat, false)
        .iter()
        .map(|&edge| ir[edge].destination)
        .collect()
}

impl Close {
    fn matches_exit(self, cx: &Cx, stat: StatId) -> bool {
        let ir = &cx.ir;
        if self.nullable {
            let StatementKind::If(branch) = ir[stat].kind else {
                return false;
            };
            let Some((FunctionType::Ne, source, target)) = condition_operands(ir, branch) else {
                return false;
            };
            Expr::variable(ir, source)
                .is_some_and(|v| v.pair() == Expr::variable(ir, self.var).unwrap().pair())
                && Expr::expr_type(cx, target) == VarType::VARTYPE_NULL
        } else {
            if !matches!(ir[stat].kind, StatementKind::BasicBlock { .. }) {
                return false;
            }
            let Some(&expr) = ir[stat].exprents.and_then(|list| ir[list].first()) else {
                return false;
            };
            let ExprKind::Invocation(call) = &ir[expr].kind else {
                return false;
            };
            call.instance
                .is_some_and(|receiver| Expr::equals(cx, receiver, self.var))
                && close_receiver(cx, expr).is_some()
        }
    }

    fn remove_exit(self, cx: &mut Cx, counters: &mut CounterContainer, stat: StatId) {
        if !self.nullable {
            let list = cx.ir[stat].exprents.unwrap();
            cx.ir[list].remove(0);
            return;
        }
        let parent = cx.ir[stat].parent.unwrap();
        if cx.ir[stat]
            .first_successor()
            .is_some_and(|edge| cx.ir[edge].closure == Some(parent))
        {
            destroy_and_flatten_statement(cx, counters, parent, stat);
        } else {
            let ir = &mut cx.ir;
            let StatementKind::If(branch) = ir[stat].kind else {
                unreachable!()
            };
            let head = ir[stat].first.unwrap();
            let body = branch.if_stat.expect("Nullable resource guard has no body");
            for &child in &[head, body] {
                for edge in ir[child].all_successors().to_vec() {
                    ir[edge].destination.remove_predecessor(ir, edge);
                    if child == body
                        && let Some(closure) = ir[edge].closure
                    {
                        ir[closure].label_edges.shift_remove(&edge);
                    }
                }
            }
            let replacement = Statement::new_empty_basic_block(ir, counters);
            stat.replace_with(ir, replacement);
        }
    }
}

fn inline_return(cx: &mut Cx, counters: &mut CounterContainer, stat: StatId, dest: StatId) {
    let ir = &cx.ir;
    let mut block = dest;
    while matches!(ir[block].kind, StatementKind::BasicBlock { .. })
        && ir[block].exprents.is_some_and(|list| ir[list].is_empty())
        && let &[edge] = ir[block].all_successors()
    {
        block = ir[edge].destination;
    }
    if !matches!(ir[block].kind, StatementKind::BasicBlock { .. }) {
        return;
    }
    let Some(list) = ir[block].exprents else {
        return;
    };
    let &[exit] = ir[list].as_slice() else { return };
    let ExprKind::Exit {
        kind: ExitType::Return,
        value: Some(value),
        ..
    } = ir[exit].kind
    else {
        return;
    };
    let breaks = dest.get_predecessor_edges(ir, EdgeType::Break.mask());
    let &[edge] = breaks.as_slice() else { return };
    let source = ir[edge].source;
    if !matches!(ir[source].kind, StatementKind::BasicBlock { .. }) {
        return;
    }
    let list = ir[source].exprents.unwrap();
    let Some((left, right)) = ir[list].last().and_then(|&last| ir[last].as_assignment()) else {
        return;
    };
    let (Some(var), Some(returned)) = (Expr::variable(ir, left), Expr::variable(ir, value)) else {
        return;
    };
    let root = std::iter::successors(Some(stat), |&s| ir[s].parent)
        .last()
        .unwrap();
    if var.pair() == returned.pair() && !Expr::is_var_referenced_in_stat(ir, left, root, &[value]) {
        Expr::replace(&mut cx.ir, exit, value, right);
        *cx.ir[list].last_mut().unwrap() = exit;
        let replacement = Statement::new_empty_basic_block(&mut cx.ir, counters);
        block.replace_with(&mut cx.ir, replacement);
    }
}
