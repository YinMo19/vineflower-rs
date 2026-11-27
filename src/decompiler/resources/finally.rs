//! The resource variable and primary exception are initialized before the outer finally.

use super::{Initializer, catches_throwable, close_receiver, resource_list};
use crate::decompiler::decompose::finish::destroy_and_flatten_statement;
use crate::decompiler::exps::{ExitType, Expr, ExprKind};
use crate::decompiler::ir::StatId;
use crate::decompiler::stats::StatementKind;
use crate::engine::{Cx, counter_container::CounterContainer};
use crate::types::VarType;

pub(super) fn recover(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    stat: StatId,
    handler: StatId,
) -> bool {
    let ir = &cx.ir;
    let &[outer, _] = &ir[handler].stats[..] else {
        return false;
    };
    let StatementKind::If(first) = ir[outer].kind else {
        return false;
    };
    let Some(StatementKind::If(second)) = first.if_stat.map(|child| &ir[child].kind) else {
        return false;
    };
    let Some(body) = second.else_stat.and_then(|block| ir[block].exprents) else {
        return false;
    };
    let &[call] = ir[body].as_slice() else {
        return false;
    };
    let Some(var) = close_receiver(cx, call) else {
        return false;
    };
    let Some(init) = ir[stat].all_predecessors().iter().find_map(|&edge| {
        let source = ir[edge].source;
        if ir[edge].destination != stat
            || !matches!(ir[source].kind, StatementKind::BasicBlock { .. })
        {
            return None;
        }
        Initializer::find(ir, source, var)
    }) else {
        return false;
    };
    let child = ir[stat].first.unwrap();
    if !matches!(ir[child].kind, StatementKind::Catch { .. }) {
        return false;
    }

    let resource = Expr::copy(cx, counters, init.expr);
    let (left, mut right) = cx.ir[resource].as_assignment().unwrap();
    if Expr::expr_type(cx, right) == VarType::VARTYPE_NULL {
        if let Some(first) = cx.ir[child].first.and_then(|s| cx.ir[s].exprents)
            && let Some((i, value)) = cx.ir[first].iter().enumerate().find_map(|(i, &expr)| {
                let (dst, value) = cx.ir[expr].as_assignment()?;
                (Expr::equals(cx, left, dst) && Expr::expr_type(cx, value) != VarType::VARTYPE_NULL)
                    .then_some((i, value))
            })
        {
            let ExprKind::Assignment { right: rhs, .. } = &mut cx.ir[resource].kind else {
                unreachable!()
            };
            *rhs = value;
            right = value;
            cx.ir[first].remove(i);
        }
        if Expr::expr_type(cx, right) == VarType::VARTYPE_NULL {
            return false;
        }
    }
    init.remove(cx);
    let resources = resource_list(&mut cx.ir, child);
    cx.ir[resources].insert(0, resource);
    let definitions = cx.ir[stat].var_definitions.clone();
    cx.ir[child].var_definitions.splice(..0, definitions);
    stat.replace_with(&mut cx.ir, child);
    destroy_and_flatten_statement(cx, counters, stat, handler);
    remove_rethrow(cx, init.block, child);
    true
}

fn remove_rethrow(cx: &mut Cx, init: StatId, stat: StatId) {
    let ir = &cx.ir;
    let StatementKind::Catch { vars, .. } = &ir[stat].kind else {
        unreachable!()
    };
    let handler = ir[stat]
        .stats
        .iter()
        .enumerate()
        .skip(1)
        .find_map(|(index, &handler)| {
            if !matches!(ir[handler].kind, StatementKind::BasicBlock { .. }) {
                return None;
            }
            let list = ir[handler].exprents?;
            let [.., previous, last] = ir[list].as_slice() else {
                return None;
            };
            let ExprKind::Exit {
                kind: ExitType::Throw,
                value: Some(thrown),
                ..
            } = ir[*last].kind
            else {
                return None;
            };
            (catches_throwable(cx, stat, index - 1) && Expr::equals(cx, thrown, vars[index - 1]))
                .then_some((index, handler, *previous))
        });
    let Some((index, handler, previous)) = handler else {
        return;
    };
    let StatementKind::Catch {
        vars, exceptions, ..
    } = &mut cx.ir[stat].kind
    else {
        unreachable!()
    };
    vars.remove(index - 1);
    exceptions.remove(index - 1);
    cx.ir[stat].stats.remove(index);
    for edge in cx.ir[handler].all_successors().to_vec() {
        edge.remove(&mut cx.ir);
    }

    let Some((left, _)) = cx.ir[previous].as_assignment() else {
        return;
    };
    if Expr::expr_type(cx, left).value.as_deref() == Some("java/lang/Throwable") {
        let list = cx.ir[init].exprents.unwrap();
        if let Some(index) = cx.ir[list].iter().position(|&expr| {
            cx.ir[expr]
                .as_assignment()
                .is_some_and(|(target, _)| Expr::equals(cx, target, left))
        }) {
            cx.ir[list].remove(index);
        }
    }
}
