// Copyright 2000-2018 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! JVM descriptor lookup for preserving Java overload selection.

use std::collections::VecDeque;
use std::sync::Arc;

use rustc_hash::FxHashSet;

use crate::code::code_constants::{
    ACC_PRIVATE, ACC_PROTECTED, ACC_PUBLIC, ACC_VARARGS, are_parameters_polymorphic,
};
use crate::decompiler::exps::{Expr, ExprKind, Invocation};
use crate::engine::Cx;
use crate::structs::{StructClass, StructMember, StructMethod};
use crate::types::{CodeType, MethodDescriptor, VarType};

pub(super) fn matched_descriptors(
    cx: &Cx,
    call: &Invocation,
    owner: &Arc<StructClass>,
    mut matcher: impl FnMut(&StructMethod, &MethodDescriptor) -> bool,
) -> Vec<Arc<StructMethod>> {
    let mut matches = Vec::new();
    let mut pending = VecDeque::from([Arc::clone(owner)]);
    let mut visited = FxHashSet::default();
    while let Some(class) = pending.pop_front() {
        for method in class
            .methods
            .iter()
            .filter(|method| method.name == call.name)
        {
            let descriptor = MethodDescriptor::parse_descriptor(&method.descriptor);
            if matcher(method, &descriptor) && can_access(cx, method) {
                matches.push(Arc::clone(method));
            }
        }
        if Arc::ptr_eq(&class, owner) && !matches.is_empty() {
            break;
        }
        visited.insert(class.qualified_name.clone());
        for ancestor in class
            .super_class
            .iter()
            .map(|parent| parent.get_string())
            .chain(&class.interface_names)
        {
            if !visited.contains(ancestor)
                && let Some(ancestor) = cx.classes().get_class(ancestor)
            {
                pending.push_back(ancestor);
            }
        }
    }
    matches
}

pub(super) fn ranks_match(
    cx: &Cx,
    call: &Invocation,
    params: &[VarType],
    left_varargs: bool,
    right_varargs: bool,
) -> bool {
    let target = &call.descriptor.params;
    params.len() == target.len()
        && params
            .iter()
            .zip(target)
            .enumerate()
            .all(|(i, (left, right))| {
                if left.type_family != right.type_family
                    && !(left.type_family.is_numeric() && right.type_family.is_numeric())
                {
                    return false;
                }
                let last = i + 1 == params.len();
                let left = left.array_dim - i32::from(left_varargs && last);
                let right = right.array_dim - i32::from(right_varargs && last);
                left == right
                    || call
                        .parameters
                        .get(i)
                        .is_some_and(|&arg| Expr::expr_type(cx, arg).ty == CodeType::Null)
            })
}

pub(super) fn can_access(cx: &Cx, method: &StructMethod) -> bool {
    let Some(current) = cx.current_class_node.as_deref() else {
        return true;
    };
    let owner = &method.class_qualified_name;
    if method.has_modifier(ACC_PUBLIC) {
        true
    } else if method.has_modifier(ACC_PRIVATE) {
        current == owner.as_str()
    } else {
        let pack = |name: &str| name.rfind('/');
        let package_matches = pack(current) == pack(owner)
            && current.get(..pack(current).unwrap_or(0)) == owner.get(..pack(owner).unwrap_or(0));
        package_matches
            || method.has_modifier(ACC_PROTECTED) && cx.classes().instance_of(current, owner)
    }
}

pub(super) fn is_varargs_ambiguous(matches: &[Arc<StructMethod>]) -> bool {
    let descriptors: Vec<_> = matches
        .iter()
        .map(|method| {
            (
                method,
                MethodDescriptor::parse_descriptor(&method.descriptor),
            )
        })
        .collect();
    descriptors.iter().any(|(method, md)| {
        descriptors.iter().any(|(other, od)| {
            !Arc::ptr_eq(method, other)
                && other.has_modifier(ACC_VARARGS)
                && md.params.len() == od.params.len()
                && md
                    .params
                    .last()
                    .zip(od.params.last())
                    .is_some_and(|(left, right)| *left == right.decrease_array_dim())
        })
    })
}

pub(super) fn ambiguous_parameters(
    cx: &Cx,
    call: &Invocation,
    matches: &[Arc<StructMethod>],
    current: Option<&Arc<StructMethod>>,
) -> Vec<bool> {
    if matches.len() == 1 {
        return Vec::new();
    }
    if call
        .classname
        .as_deref()
        .is_some_and(|class| are_parameters_polymorphic(class, &call.name))
    {
        return vec![true; call.parameters.len()];
    }
    let arg_types: Vec<_> = call
        .parameters
        .iter()
        .map(|&arg| {
            let operand = match &cx.ir[arg].kind {
                ExprKind::Function {
                    operands,
                    needs_cast: false,
                    ..
                } => operands.first().copied().unwrap_or(arg),
                _ => arg,
            };
            Expr::expr_type(cx, operand)
        })
        .collect();
    let mut seen = FxHashSet::default();
    let mut possible = Vec::new();
    let mut exacts = Vec::new();
    for method in matches
        .iter()
        .filter(|method| seen.insert(Arc::as_ptr(method)))
    {
        let md = MethodDescriptor::parse_descriptor(&method.descriptor);
        if md
            .params
            .iter()
            .zip(&arg_types)
            .all(|(param, arg)| *param == *arg || arg.ty == CodeType::Null)
        {
            exacts.push(method);
        }
        // Upstream adds one method when any position is assignable.
        if md
            .params
            .iter()
            .zip(&arg_types)
            .any(|(param, arg)| param.higher_cross_family_than(cx, arg, true))
        {
            possible.push(md);
        }
    }
    if possible.len() == 1
        || exacts.is_empty()
        || matches!(exacts.as_slice(), [exact] if current.is_some_and(|current| Arc::ptr_eq(exact, current)))
    {
        return Vec::new();
    }
    let current_descriptor =
        current.map(|method| MethodDescriptor::parse_descriptor(&method.descriptor));
    let expected = current_descriptor.as_ref().unwrap_or(&call.descriptor);
    let mut ambiguous = vec![false; arg_types.len()];
    for method in possible {
        for (i, ((desired, other), actual)) in expected
            .params
            .iter()
            .zip(&method.params)
            .zip(&arg_types)
            .enumerate()
        {
            if desired != other
                && (desired.higher_cross_family_than(cx, other, false)
                    || actual == other
                    || actual.ty == CodeType::Null)
            {
                ambiguous[i] = true;
            }
        }
    }
    ambiguous
}
