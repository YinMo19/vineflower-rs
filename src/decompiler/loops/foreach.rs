// Copyright 2000-2020 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Enhanced for loops recovered from iterator calls or array traversal.

use std::io;

use super::{inherit_offsets, is_var_used_before, last_direct_data, preceding_data, remove_expr};
use crate::decompiler::exps::{Expr, ExprKind, FunctionType, Invocation};
use crate::decompiler::ir::{ExprId, ExprListId, Ir, StatId};
use crate::decompiler::stats::{DoStatement, LoopType, StatementKind};
use crate::engine::Cx;

#[derive(Clone, Copy)]
struct Assignment {
    expr: ExprId,
    left: ExprId,
    right: ExprId,
}

impl Assignment {
    fn read(ir: &Ir, expr: ExprId) -> Option<Self> {
        match ir[expr].kind {
            ExprKind::Assignment { left, right, .. } => Some(Self { expr, left, right }),
            _ => None,
        }
    }
}

struct ForEach {
    stat: StatId,
    initial_list: ExprListId,
    first_list: ExprListId,
    initial: Assignment,
    element: Assignment,
    setup: [Option<Assignment>; 2],
    condition: ExprId,
    header: DoStatement,
}

pub(super) fn match_for_each(cx: &mut Cx, root: StatId, stat: StatId) -> io::Result<bool> {
    let ir = &cx.ir;
    let StatementKind::Do(header) = ir[stat].kind else {
        unreachable!("Enhanced for loop candidate must be a loop");
    };
    let Some(condition) = header
        .condition(ir)
        .filter(|_| header.ty == LoopType::While)
    else {
        return Ok(false);
    };
    let Some(preceding) = preceding_data(ir, stat, false) else {
        return Ok(false);
    };
    let body = ir[stat].first.expect("Loop has no body");
    let Some(first_list) = first_direct_list(ir, body) else {
        return Ok(false);
    };
    let Some(element) = Assignment::read(ir, ir[first_list][0]) else {
        return Ok(false);
    };
    let initial_list = ir[preceding].exprents.unwrap();
    let mut previous = ir[initial_list]
        .iter()
        .rev()
        .map(|&expr| Assignment::read(ir, expr));
    let Some(initial) = previous.next().flatten() else {
        return Ok(false);
    };
    let candidate = ForEach {
        stat,
        initial_list,
        first_list,
        initial,
        element,
        setup: [previous.next().flatten(), previous.next().flatten()],
        condition,
        header,
    };
    if let Some(iterator) = iterator_call(cx, initial.right) {
        if iterator
            .classname
            .as_deref()
            .is_some_and(|name| name.contains("java/util/stream"))
        {
            return Ok(false);
        }
        candidate.match_iterator(cx, root)
    } else {
        Ok(candidate.match_array(cx, root, body))
    }
}

impl ForEach {
    fn match_iterator(&self, cx: &mut Cx, root: StatId) -> io::Result<bool> {
        let ir = &cx.ir;
        let condition = drill_nots(ir, self.condition);
        let Some(has_next) = iterator_method(cx, condition, "hasNext", "()Z") else {
            return Ok(false);
        };
        let Some(next) =
            next_call(cx, self.element.right).or_else(|| next_unboxing(cx, self.element.right))
        else {
            return Ok(false);
        };
        if Expr::variable(ir, self.element.left).is_none() {
            return Ok(false);
        }
        let Some(next_var) = next
            .instance
            .filter(|&expr| Expr::variable(ir, expr).is_some())
        else {
            return Ok(false);
        };
        let Some(has_next_var) = has_next
            .instance
            .filter(|&expr| Expr::variable(ir, expr).is_some())
        else {
            return Ok(false);
        };
        let iterator_var = self.initial.left;
        let Some(iterator) = Expr::variable(ir, iterator_var) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "Iterator assignment has no local variable",
            ));
        };
        let iterator_index = iterator.index;
        if Expr::is_var_referenced_in_stat(ir, iterator_var, self.stat, &[next_var, has_next_var])
            || !same_version(ir, iterator_var, next_var)
        {
            return Ok(false);
        }

        if let ExprKind::Function {
            op: FunctionType::Cast,
            ref operands,
            ..
        } = ir[self.initial.right].kind
            && matches!(ir[operands[0]].kind, ExprKind::Invocation(_))
        {
            return Ok(false);
        }
        if is_var_used_before(&mut cx.ir, root, self.stat, self.element.left)
            || is_var_used_after(&cx.ir, self.stat, iterator_index)
        {
            return Ok(false);
        }
        let ir = &mut cx.ir;
        let ExprKind::Invocation(holder) = &ir[self.initial.right].kind else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "Iterator assignment has nested casts",
            ));
        };
        let Some(iterable) = holder.instance else {
            return Ok(false);
        };

        Expr::add_bytecode_range(ir, iterable, self.initial.expr);
        Expr::add_bytecode_range(ir, iterable, self.initial.right);
        Expr::add_bytecode_range(ir, self.element.left, self.element.expr);
        Expr::add_bytecode_range(ir, self.element.left, self.element.right);
        if let Some(increment) = self.header.increment(ir) {
            Expr::add_bytecode_range(ir, iterable, increment);
        }
        if let Some(init) = self.header.init(ir) {
            Expr::add_bytecode_range(ir, self.element.left, init);
        }
        self.promote(cx, iterable);
        remove_expr(cx, self.initial_list, self.initial.expr);
        remove_expr(cx, self.first_list, self.element.expr);

        if let Some(copy) = self.setup[0]
            && same_version(&cx.ir, copy.left, iterable)
            && !Expr::is_var_referenced_in_stat(&cx.ir, iterable, root, &[copy.left])
            && next_call(cx, copy.right).is_none()
        {
            remove_expr(cx, self.initial_list, copy.expr);
            Expr::add_bytecode_range(&mut cx.ir, copy.right, copy.expr);
            Expr::add_bytecode_range(&mut cx.ir, copy.right, iterable);
            self.stat.set_loop_increment(&mut cx.ir, copy.right);
        }
        self.retain_bound(cx);
        Ok(true)
    }

    fn match_array(&self, cx: &mut Cx, root: StatId, body: StatId) -> bool {
        let ir = &cx.ir;
        let Some(length) = self.setup[0] else {
            return false;
        };
        let ExprKind::Array { array, index, .. } = ir[self.element.right].kind else {
            return false;
        };
        if Expr::variable(ir, self.element.left).is_none()
            || Expr::variable(ir, index).is_none()
            || !matches!(ir[self.initial.right].kind, ExprKind::Constant { .. })
            || !matches!(ir[self.condition].kind, ExprKind::Function { .. })
        {
            return false;
        }
        let ExprKind::Function {
            op: FunctionType::ArrayLength,
            ref operands,
            ..
        } = ir[length.right].kind
        else {
            return false;
        };
        let length_array = operands[0];
        let Some(last_list) = last_direct_data(ir, body).and_then(|stat| ir[stat].exprents) else {
            return false;
        };
        let Some(&increment) = ir[last_list].last() else {
            return false;
        };
        let ExprKind::Function {
            op: FunctionType::Ppi | FunctionType::Ipp,
            ref operands,
            ..
        } = ir[increment].kind
        else {
            return false;
        };
        let counter = operands[0];
        if Expr::variable(ir, counter).is_some()
            && (!same_version(ir, counter, index)
                || Expr::is_var_referenced_in_stat(ir, counter, body, &[index]))
        {
            return false;
        }
        if !same_version(ir, array, length_array)
            || is_var_used_before(&mut cx.ir, root, self.stat, self.element.left)
        {
            return false;
        }

        for source in [self.initial.expr, length.expr, increment] {
            inherit_offsets(&mut cx.ir, length_array, source);
        }
        for source in [self.element.expr, self.initial.expr] {
            inherit_offsets(&mut cx.ir, self.element.left, source);
        }
        self.promote(cx, length_array);
        remove_expr(cx, self.initial_list, self.initial.expr);
        remove_expr(cx, self.initial_list, length.expr);
        remove_expr(cx, self.first_list, self.element.expr);
        remove_expr(cx, last_list, increment);

        if let Some(copy) = self.setup[1]
            && same_version(&cx.ir, copy.left, array)
            && !Expr::is_var_referenced_in_stat(
                &cx.ir,
                copy.left,
                cx.ir[self.stat].parent.expect("Loop has no parent"),
                &[length_array],
            )
        {
            remove_expr(cx, self.initial_list, copy.expr);
            inherit_offsets(&mut cx.ir, copy.right, copy.expr);
            inherit_offsets(&mut cx.ir, copy.right, length_array);
            self.stat.set_loop_increment(&mut cx.ir, copy.right);
        }
        self.retain_bound(cx);
        true
    }

    fn promote(&self, cx: &mut Cx, iterable: ExprId) {
        self.stat.set_loop_type(&mut cx.ir, LoopType::ForEach);
        self.stat.set_loop_init(&mut cx.ir, self.element.left);
        self.stat.set_loop_increment(&mut cx.ir, iterable);
    }

    fn retain_bound(&self, cx: &mut Cx) {
        let (_, bound) = Expr::assignment_bound(cx, self.element.left, self.element.right);
        let ExprKind::Variable(var) = &mut cx.ir[self.element.left].kind else {
            unreachable!("Loop element must be a variable");
        };
        var.bound_type = Some(Box::new(bound));
    }
}

fn same_version(ir: &Ir, left: ExprId, right: ExprId) -> bool {
    Expr::variable(ir, left)
        .zip(Expr::variable(ir, right))
        .is_some_and(|(left, right)| left.pair() == right.pair())
}

fn is_var_used_after(ir: &Ir, stat: StatId, index: i32) -> bool {
    let Some(parent) = ir[stat]
        .parent
        .filter(|&parent| matches!(ir[parent].kind, StatementKind::Sequence))
    else {
        return false;
    };
    ir[parent]
        .stats
        .iter()
        .copied()
        .skip_while(|&sibling| sibling != stat)
        .skip(1)
        .any(|sibling| is_var_used_in(ir, sibling, index))
}

fn is_var_used_in(ir: &Ir, stat: StatId, index: i32) -> bool {
    ir[stat]
        .stats
        .iter()
        .any(|&child| is_var_used_in(ir, child, index))
        || stat
            .stat_exprents(ir)
            .into_iter()
            .any(|expr| Expr::contains_var_index(ir, expr, index))
        || ir[stat].exprents.is_some_and(|list| {
            ir[list]
                .iter()
                .any(|&expr| Expr::contains_var_index(ir, expr, index))
        })
}

fn first_direct_list(ir: &Ir, stat: StatId) -> Option<ExprListId> {
    ir[stat]
        .exprents
        .filter(|&list| !ir[list].is_empty())
        .or_else(|| {
            ir[stat]
                .stats
                .iter()
                .find_map(|&child| first_direct_list(ir, child))
        })
}

fn drill_nots(ir: &Ir, mut expr: ExprId) -> ExprId {
    while let ExprKind::Function { op, operands, .. } = &ir[expr].kind {
        match op {
            FunctionType::BoolNot => expr = operands[0],
            FunctionType::Eq | FunctionType::Ne => return operands[0],
            _ => break,
        }
    }
    expr
}

fn as_invocation(ir: &Ir, mut expr: ExprId) -> Option<&Invocation> {
    while let ExprKind::Function {
        op: FunctionType::Cast,
        operands,
        ..
    } = &ir[expr].kind
    {
        expr = operands[0];
    }
    match &ir[expr].kind {
        ExprKind::Invocation(invoke) => Some(invoke),
        _ => None,
    }
}

fn iterator_call(cx: &Cx, expr: ExprId) -> Option<&Invocation> {
    let invoke = as_invocation(&cx.ir, expr)?;
    (matches!(invoke.name.as_str(), "iterator" | "listIterator")
        && invoke
            .descriptor
            .ret
            .value
            .as_deref()
            .is_some_and(|class| is_iterator(cx, class)))
    .then_some(invoke)
}

fn iterator_method<'a>(
    cx: &'a Cx,
    expr: ExprId,
    name: &str,
    descriptor: &str,
) -> Option<&'a Invocation> {
    let invoke = as_invocation(&cx.ir, expr)?;
    (invoke.name.as_str() == name
        && invoke.string_descriptor() == descriptor
        && invoke
            .classname
            .as_deref()
            .is_some_and(|class| is_iterator(cx, class)))
    .then_some(invoke)
}

fn is_iterator(cx: &Cx, class: &str) -> bool {
    cx.classes().instance_of(class, "java/util/Iterator")
}

fn next_call(cx: &Cx, expr: ExprId) -> Option<&Invocation> {
    iterator_method(cx, expr, "next", "()Ljava/lang/Object;")
}

fn next_unboxing(cx: &Cx, expr: ExprId) -> Option<&Invocation> {
    let invoke = as_invocation(&cx.ir, expr)?;
    if invoke.is_unboxing_call() {
        next_call(cx, invoke.instance?)
    } else {
        None
    }
}
