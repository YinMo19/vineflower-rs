// Copyright 2000-2018 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Constructor, lambda, and qualified-allocation patterns.

use std::collections::VecDeque;

use super::{set_assignment_right, variable};
use crate::decompiler::exps::{Expr, ExprKind, InvocationFunction, InvocationType};
use crate::decompiler::ir::{ExprId, ExprListId, Ir};
use crate::decompiler::sforms::SsaResult;
use crate::decompiler::vars::var_version_pair::VarVersionPair;
use crate::engine::Cx;
use crate::engine::class_nodes::ClassKind;
use crate::engine::counter_container::CounterContainer;
use crate::structs::StructClass;
use crate::types::{CodeType, VarType};

pub(super) fn simple(ir: &mut Ir, expr: ExprId) -> Option<ExprId> {
    let children: Vec<_> = Expr::children(ir, expr).collect();
    for child in children {
        if let Some(replacement) = simple(ir, child) {
            Expr::replace(ir, expr, child, replacement);
        }
    }

    let ExprKind::Invocation(invocation) = &ir[expr].kind else {
        return None;
    };
    let allocation = invocation.instance?;
    if invocation.function != InvocationFunction::Init
        || !matches!(ir[allocation].kind, ExprKind::New { .. })
    {
        return None;
    }
    attach(ir, allocation, expr, false);
    Some(allocation)
}

pub(super) fn lambda(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    expr: ExprId,
    class: &StructClass,
) -> Option<ExprId> {
    let children: Vec<_> = Expr::children(&cx.ir, expr).collect();
    for child in children {
        if let Some(replacement) = lambda(cx, counters, child, class) {
            Expr::replace(&mut cx.ir, expr, child, replacement);
        }
    }

    let ExprKind::Invocation(invocation) = &cx.ir[expr].kind else {
        return None;
    };
    if invocation.kind != InvocationType::Dynamic {
        return None;
    }
    let name = format!(
        "{}{}",
        class.qualified_name,
        invocation.dynamic_class_suffix.as_deref()?
    );
    cx.class_nodes.allocation_class(&name)?;

    let ty = VarType::from_signature_cl(&name, true);
    let offsets = cx.ir[expr].bytecode.clone();
    let allocation = Expr::new_allocation(cx, counters, ty, Vec::new(), offsets);
    attach(&mut cx.ir, allocation, expr, true);
    Some(allocation)
}

pub(super) fn swap(
    ir: &mut Ir,
    list: ExprListId,
    index: usize,
    current: ExprId,
    next: ExprId,
) -> bool {
    let previous = ir[list][index - 1];
    let (Some((left, allocation)), Some((_, alias))) =
        (ir[previous].as_assignment(), ir[current].as_assignment())
    else {
        return false;
    };
    if !matches!(ir[allocation].kind, ExprKind::New { .. }) {
        return false;
    }
    let ExprKind::Invocation(invoke) = &ir[next].kind else {
        return false;
    };
    let (Some(left), Some(alias), Some(receiver)) = (
        variable(ir, left),
        variable(ir, alias),
        invoke.instance.and_then(|expr| variable(ir, expr)),
    ) else {
        return false;
    };
    if invoke.function != InvocationFunction::Init
        || left.index != alias.index
        || alias.index != receiver.index
    {
        return false;
    }
    attach(ir, allocation, next, false);
    set_assignment_right(ir, current, allocation);
    true
}

pub(super) fn remote(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    list: ExprListId,
    index: usize,
    current: ExprId,
) -> bool {
    let Some((left, allocation)) = cx.ir[current].as_assignment() else {
        return false;
    };
    let Some(var) = variable(&cx.ir, left) else {
        return false;
    };
    let ExprKind::New {
        new_type,
        constructor: None,
        ..
    } = &cx.ir[allocation].kind
    else {
        return false;
    };
    if new_type.ty != CodeType::Object || new_type.array_dim != 0 {
        return false;
    }
    let pair = VarVersionPair::new(var.index, var.version);
    for i in index + 1..cx.ir[list].len() {
        let candidate = cx.ir[list][i];
        if let ExprKind::Invocation(invoke) = &cx.ir[candidate].kind
            && invoke.function == InvocationFunction::Init
            && let Some(receiver) = invoke.instance
            && variable(&cx.ir, receiver).is_some()
            && Expr::equals(cx, left, receiver)
        {
            attach(&mut cx.ir, allocation, candidate, false);
            cx.ir[list][i] = Expr::copy(cx, counters, current);
            return true;
        }

        if Expr::all_exprents(&cx.ir, candidate, true, true)
            .into_iter()
            .any(|expr| variable(&cx.ir, expr).is_some_and(|v| pair.is(v.index, v.version)))
        {
            // An intervening use prevents relocation of the allocation.
            return false;
        }
    }
    false
}

pub(super) fn qualified_new_get_class(cx: &Cx, first: ExprId, second: ExprId) -> bool {
    let ExprKind::Invocation(invoke) = &cx.ir[first].kind else {
        return false;
    };
    let name = invoke.name.as_str();
    let descriptor = invoke.string_descriptor();
    let recognized = if invoke.is_static {
        invoke.classname.as_deref() == Some("java/util/Objects")
            && name == "requireNonNull"
            && descriptor == "(Ljava/lang/Object;)Ljava/lang/Object;"
    } else {
        name == "getClass" && descriptor == "()Ljava/lang/Class;"
    };
    if !recognized {
        return false;
    }
    if invoke.synthetic_null_check {
        return true;
    }
    let target = if invoke.is_static {
        invoke.parameters.first().copied()
    } else {
        invoke.instance
    };
    let Some(target) = target else {
        return false;
    };
    let mut remaining = VecDeque::from([second]);
    while let Some(expr) = remaining.pop_front() {
        remaining.extend(Expr::children(&cx.ir, expr));
        if let ExprKind::New {
            new_type,
            constructor: Some(constructor),
            ..
        } = &cx.ir[expr].kind
            && let ExprKind::Invocation(ctor) = &cx.ir[*constructor].kind
            && let Some(&first_param) = ctor.parameters.first()
            && (Expr::equals(cx, first_param, target)
                || is_unambiguously_same_param(cx, invoke.is_static, target, &ctor.parameters))
            && cx
                .class_nodes
                .allocation_class(new_type.name())
                .is_some_and(|node| node.kind != ClassKind::Root)
        {
            return true;
        }
    }
    false
}

fn is_unambiguously_same_param(
    cx: &Cx,
    is_static: bool,
    target: ExprId,
    params: &[ExprId],
) -> bool {
    let target_type = Expr::expr_type(cx, target);
    Expr::expr_type(cx, params[0]) == target_type
        && (!is_static
            || params[1..]
                .iter()
                .all(|&param| Expr::expr_type(cx, param) != target_type))
}

pub(super) fn inline_method_reference_assignment(
    cx: &mut Cx,
    ssa: &SsaResult,
    class: &StructClass,
    first: ExprId,
    second: ExprId,
) -> bool {
    let Some((left, right)) = cx.ir[first].as_assignment() else {
        return false;
    };
    let Some(var) = variable(&cx.ir, left) else {
        return false;
    };
    if Expr::expr_type(cx, left).ty != CodeType::Object
        || var.lvt.is_some()
        || ssa
            .read_counts
            .get(&VarVersionPair::new(var.index, var.version))
            != Some(&1)
    {
        return false;
    }
    for expr in Expr::all_exprents(&cx.ir, second, true, false) {
        if let ExprKind::New {
            new_type,
            constructor: Some(constructor),
            lambda: true,
            method_reference: false,
            ..
        } = &cx.ir[expr].kind
            && let ExprKind::Invocation(invoke) = &cx.ir[*constructor].kind
            && let [parameter] = invoke.parameters.as_slice()
            && Expr::contains(cx, *constructor, left)
            && let Some(info) = cx
                .class_nodes
                .allocation_class(new_type.name())
                .and_then(|node| node.lambda)
            && cx
                .method_properties(class, &info.content_method_key)
                .is_some_and(|properties| properties.is_synthetic_reference_lambda)
        {
            let (constructor, parameter) = (*constructor, *parameter);
            Expr::replace(&mut cx.ir, constructor, parameter, right);
            return true;
        }
    }
    false
}

fn attach(ir: &mut Ir, allocation: ExprId, invocation: ExprId, keep_instance: bool) {
    let ExprKind::New { constructor, .. } = &mut ir[allocation].kind else {
        unreachable!()
    };
    *constructor = Some(invocation);
    if !keep_instance {
        let ExprKind::Invocation(invoke) = &mut ir[invocation].kind else {
            unreachable!()
        };
        invoke.instance = None;
    }
}
