//! Recognize the cleanup protocols emitted for Java try-with-resources.

mod finally;
mod suppressed;

use super::decompose::finish::condense_sequences;
use super::exps::{Expr, ExprKind};
use super::ir::{ExprId, ExprListId, Ir, StatId};
use super::stats::StatementKind;
use crate::engine::{Cx, counter_container::CounterContainer};
use crate::structs::StructClass;

pub(crate) fn enhance(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    root: StatId,
    class: &StructClass,
) -> bool {
    let cx = &mut *cx.enter_method(counters);
    let recovered = recover(
        cx,
        counters,
        root,
        class.version.has_new_try_with_resources(),
    );
    if recovered {
        condense_sequences(cx, counters, root);
    }
    let merged = merge_nested(&mut cx.ir, root);
    if merged {
        condense_sequences(cx, counters, root);
    }
    recovered || merged
}

fn recover(cx: &mut Cx, counters: &mut CounterContainer, stat: StatId, modern: bool) -> bool {
    let mut changed = match cx.ir[stat].kind {
        StatementKind::Catch { .. } if modern => suppressed::recover(cx, counters, stat),
        StatementKind::CatchAll {
            is_finally: true,
            handler: Some(handler),
            ..
        } => finally::recover(cx, counters, stat, handler),
        _ => false,
    };
    let children = cx.ir[stat].stats.to_vec();
    for child in children {
        changed |= recover(cx, counters, child, modern);
    }
    changed
}

fn merge_nested(ir: &mut Ir, stat: StatId) -> bool {
    let mut changed = matches!(ir[stat].kind, StatementKind::Catch { .. }) && merge(ir, stat);
    let children = ir[stat].stats.to_vec();
    for child in children {
        changed |= merge_nested(ir, child);
    }
    changed
}

fn merge(ir: &mut Ir, outer: StatId) -> bool {
    let Some(&inner) = ir[outer].stats.first() else {
        return false;
    };
    let inner = if matches!(ir[inner].kind, StatementKind::Sequence)
        && outer.edges_leaving(ir, inner, false).is_empty()
    {
        ir[inner].stats[0]
    } else {
        inner
    };
    let StatementKind::Catch {
        resources: Some(list),
        ..
    } = ir[inner].kind
    else {
        return false;
    };
    let &[body] = &ir[inner].stats[..] else {
        return false;
    };
    if ir[list].is_empty() {
        return false;
    }
    let resources = resource_list(ir, outer);
    let additions = ir[list].clone();
    ir[resources].extend(additions);
    let definitions = ir[inner].var_definitions.clone();
    ir[outer].var_definitions.extend(definitions);

    let redundant: Vec<_> = ir[body]
        .all_successors()
        .iter()
        .copied()
        .filter(|&edge| {
            ir[inner]
                .all_successors()
                .iter()
                .any(|&exit| ir[exit].destination == ir[edge].destination)
        })
        .collect();
    for edge in redundant {
        edge.remove(ir);
    }
    inner.replace_with(ir, body);
    true
}

fn resource_list(ir: &mut Ir, stat: StatId) -> ExprListId {
    let StatementKind::Catch { resources, .. } = ir[stat].kind else {
        unreachable!("Resources belong to a catch statement")
    };
    if let Some(list) = resources {
        return list;
    }
    let list = ir.new_list(Vec::new());
    let StatementKind::Catch { resources, .. } = &mut ir[stat].kind else {
        unreachable!()
    };
    *resources = Some(list);
    list
}

fn close_receiver(cx: &Cx, expr: ExprId) -> Option<ExprId> {
    let ExprKind::Invocation(call) = &cx.ir[expr].kind else {
        return None;
    };
    let receiver = call.instance?;
    if call.name != "close"
        || call.string_descriptor() != "()V"
        || Expr::variable(&cx.ir, receiver).is_none()
        || !cx
            .classes()
            .instance_of(call.classname.as_deref()?, "java/lang/AutoCloseable")
    {
        return None;
    }
    Some(receiver)
}

#[derive(Clone, Copy)]
struct Initializer {
    block: StatId,
    expr: ExprId,
}

impl Initializer {
    /// The type of the initializer can still be unknown; Java compares slot and version.
    fn find(ir: &Ir, block: StatId, var: ExprId) -> Option<Self> {
        let pair = Expr::variable(ir, var)?.pair();
        let list = ir[block].exprents?;
        ir[list].iter().find_map(|&expr| {
            let (left, _) = ir[expr].as_assignment()?;
            (Expr::variable(ir, left)?.pair() == pair).then_some(Self { block, expr })
        })
    }

    fn remove(self, cx: &mut Cx) {
        let list = cx.ir[self.block].exprents.unwrap();
        if let Some(index) = cx.ir[list]
            .iter()
            .position(|&expr| Expr::equals(cx, self.expr, expr))
        {
            cx.ir[list].remove(index);
        }
    }
}

fn catches_throwable(cx: &Cx, stat: StatId, index: usize) -> bool {
    let StatementKind::Catch { vars, .. } = &cx.ir[stat].kind else {
        return false;
    };
    vars.get(index).is_some_and(|&var| {
        Expr::expr_type(cx, var).value.as_deref() == Some("java/lang/Throwable")
    })
}
