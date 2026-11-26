// Copyright 2000-2020 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Lift field assignments from the static initializer and constructor prefixes.

use std::io;
use std::sync::Arc;

use arcstr::ArcStr;
use indexmap::IndexSet;
use rustc_hash::{FxHashMap, FxHashSet};

use crate::code::code_constants::{
    ACC_ENUM, ACC_FINAL, ACC_INTERFACE, ACC_STATIC, ACC_SYNTHETIC, INIT_NAME,
};
use crate::decompiler::exps::{
    Expr, ExprKind, Field, FunctionType, Invocation, InvocationFunction,
};
use crate::decompiler::exps::expr_util::synthetic_parameters_mask;
use crate::decompiler::ir::{ExprId, ExprListId, Ir, StatId, VarProcessorId};
use crate::decompiler::stats::StatementKind;
use crate::engine::Cx;
use crate::engine::class_nodes::{ClassKind, ClassNodeId};
use crate::engine::class_wrapper::{MethodSlot, catch_method_failure};
use crate::structs::{StructClass, StructMember};
use crate::types::CodeType;
use crate::util::interpreter_util::make_unique_key;

pub(crate) fn extract(cx: &mut Cx, node: ClassNodeId) -> io::Result<()> {
    let class = Arc::clone(&cx.class_nodes[node].class);
    if let Some(method) = MethodSlot::by_key(cx, node, "<clinit> ()V")
        && let Some(root) = method.get(cx).root()
        && let Err(error) = catch_method_failure(|| extract_static(cx, node, &class, method, root))
    {
        if error.kind() == io::ErrorKind::Interrupted {
            return Err(error);
        }
        log::warn!(
            "Method <clinit> ()V in class {} couldn't be written: {error}",
            class.qualified_name
        );
        method.get_mut(cx).write_error = Some(error);
    }

    let constructors: Vec<_> = cx.class_nodes[node]
        .wrapper
        .as_ref()
        .ok_or_else(|| invalid("Missing class wrapper for initializers"))?
        .methods
        .iter()
        .enumerate()
        .filter(|(_, method)| method.method.name == INIT_NAME)
        .filter_map(|(index, method)| method.root().map(|root| (MethodSlot { node, index }, root)))
        .collect();
    extract_dynamic(cx, node, &class, &constructors)?;
    lift_constructor(cx, &class, &constructors);
    if cx.options.hide_empty_super {
        hide_empty_super(cx, &class, &constructors)?;
    }
    Ok(())
}

pub(super) fn first_data(ir: &Ir, mut stat: StatId) -> Option<ExprListId> {
    loop {
        if let Some(list) = ir[stat].exprents {
            return Some(list);
        }
        if stat.is_labeled(ir)
            || !matches!(
                ir[stat].kind,
                StatementKind::Sequence
                    | StatementKind::If(_)
                    | StatementKind::Root { .. }
                    | StatementKind::Switch(_)
                    | StatementKind::Synchronized { .. }
            )
        {
            return None;
        }
        stat = ir[stat].first?;
    }
}

pub(super) fn constructor_call(
    cx: &Cx,
    method: MethodSlot,
    class: &StructClass,
    expr: ExprId,
    allow_this: bool,
) -> bool {
    let ExprKind::Invocation(call) = &cx.ir[expr].kind else {
        return false;
    };
    call.function == InvocationFunction::Init
        && call
            .instance
            .and_then(|expr| Expr::variable(&cx.ir, expr))
            .is_some_and(|variable| {
                cx.ir[method.get(cx).variables]
                    .this_vars
                    .get(&variable.pair())
                    .is_some()
            })
        && (allow_this || call.classname.as_ref() != Some(&class.qualified_name))
}

fn extract_static(
    cx: &mut Cx,
    node: ClassNodeId,
    class: &StructClass,
    method: MethodSlot,
    root: StatId,
) -> io::Result<()> {
    if let Some(list) = first_data(&cx.ir, root) {
        let always_inline = class.has_modifier(ACC_INTERFACE) || class.has_modifier(ACC_ENUM);
        let variables = method.get(cx).variables;
        let multiple = multiply_assigned_fields(&cx.ir, list);
        let mut remaining = Vec::new();
        let mut locals = FxHashMap::default();
        let mut consumed = Vec::new();
        let mut i = 0;
        while i < cx.ir[list].len() {
            let expr = cx.ir[list][i];
            let Some((left, right)) = cx.ir[expr].as_assignment() else {
                i += 1;
                continue;
            };
            if let ExprKind::Field(field) = &cx.ir[left].kind {
                if let Some((index, key)) = declared_field(class, field, true) {
                    let context = InitializerContext::Static {
                        multiple: &multiple,
                        remaining: &remaining,
                    };
                    let independent = is_independent(cx, class, variables, right, index, context)?;
                    if !always_inline && !independent {
                        remaining.push(left);
                    } else if !cx.class_nodes[node]
                        .wrapper
                        .as_ref()
                        .unwrap()
                        .static_field_initializers
                        .contains_key(key.as_str())
                        && (independent
                            || inline_new_receiver(&mut cx.ir, right, &mut locals, &mut consumed))
                    {
                        cx.class_nodes[node]
                            .wrapper
                            .as_mut()
                            .unwrap()
                            .static_field_initializers
                            .add_with_key(right, key);
                        cx.ir[list].remove(i);
                        continue;
                    }
                }
            } else if always_inline && let Some(var) = Expr::variable(&cx.ir, left) {
                locals.insert(var.index, expr);
            }
            i += 1;
        }
        // ArrayList.removeAll matches equivalent statements as well as aliases.
        if !consumed.is_empty() {
            let mut i = 0;
            while i < cx.ir[list].len() {
                let expr = cx.ir[list][i];
                if consumed
                    .iter()
                    .any(|&assignment| Expr::equals(cx, assignment, expr))
                {
                    cx.ir[list].remove(i);
                } else {
                    i += 1;
                }
            }
        }
    }

    if class.has_modifier(ACC_ENUM)
        && class.fields.iter().any(|field| {
            field.has_modifier(ACC_ENUM)
                && !cx.class_nodes[node]
                    .wrapper
                    .as_ref()
                    .unwrap()
                    .static_field_initializers
                    .contains_key(make_unique_key(&field.name, &field.descriptor).as_str())
        })
    {
        let method = method.get_mut(cx);
        method.add_comment("$VF: Failed to inline enum fields");
        method.add_error_comment = true;
    }
    Ok(())
}

fn multiply_assigned_fields(ir: &Ir, list: ExprListId) -> FxHashSet<ArcStr> {
    let mut seen = FxHashSet::default();
    let mut multiple = FxHashSet::default();
    for &expr in &ir[list] {
        if let Some((left, _)) = ir[expr].as_assignment()
            && let ExprKind::Field(field) = &ir[left].kind
            && !seen.insert(field.name.clone())
        {
            multiple.insert(field.name.clone());
        }
    }
    multiple
}

fn declared_field(
    class: &StructClass,
    field: &Field,
    static_field: bool,
) -> Option<(usize, String)> {
    if field.is_static() != static_field || field.classname.as_ref() != Some(&class.qualified_name)
    {
        return None;
    }
    let key = make_unique_key(&field.name, &field.descriptor.descriptor_string);
    Some((class.fields.index_of_key(key.as_str())?, key))
}

fn inline_new_receiver(
    ir: &mut Ir,
    expr: ExprId,
    locals: &mut FxHashMap<i32, ExprId>,
    consumed: &mut Vec<ExprId>,
) -> bool {
    let ExprKind::New {
        constructor: Some(constructor),
        ..
    } = ir[expr].kind
    else {
        return false;
    };
    let ExprKind::Invocation(call) = &ir[constructor].kind else {
        unreachable!("NewExprent's constructor must be an invocation");
    };
    let Some(assignment) = call
        .instance
        .and_then(|expr| Expr::variable(ir, expr))
        .and_then(|variable| locals.remove(&variable.index))
    else {
        return false;
    };
    let (_, value) = ir[assignment].as_assignment().unwrap();
    let ExprKind::Invocation(call) = &mut ir[constructor].kind else {
        unreachable!();
    };
    call.instance = Some(value);
    consumed.push(assignment);
    true
}

fn extract_dynamic(
    cx: &mut Cx,
    node: ClassNodeId,
    class: &StructClass,
    constructors: &[(MethodSlot, StatId)],
) -> io::Result<()> {
    let anonymous = cx.class_nodes[node].kind == ClassKind::Anonymous;
    let index = usize::from(!anonymous);
    let lists: Vec<_> = constructors
        .iter()
        .filter_map(|&(method, root)| {
            let list = first_data(&cx.ir, root)?;
            let expr = *cx.ir[list].first()?;
            (anonymous || constructor_call(cx, method, class, expr, false))
                .then_some((method, list))
        })
        .collect();
    if lists.is_empty() {
        return Ok(());
    }

    let mut available: FxHashSet<_> = cx.class_nodes[node]
        .wrapper
        .as_ref()
        .unwrap()
        .static_field_initializers
        .lst_keys()
        .iter()
        .flatten()
        .cloned()
        .collect();
    let mut previous = 0;
    while let Some((key, value)) =
        common_assignment(cx, class, &lists, index, &available, &mut previous)?
    {
        if cx.class_nodes[node]
            .wrapper
            .as_ref()
            .unwrap()
            .dynamic_field_initializers
            .contains_key(key.as_str())
        {
            break;
        }
        let value = process_dynamic_initializer(&mut cx.ir, value);
        available.insert(key.clone());
        cx.class_nodes[node]
            .wrapper
            .as_mut()
            .unwrap()
            .dynamic_field_initializers
            .add_with_key(value, key);
        for &(_, list) in &lists {
            cx.ir[list].remove(index);
        }
    }
    Ok(())
}

fn common_assignment(
    cx: &mut Cx,
    class: &StructClass,
    lists: &[(MethodSlot, ExprListId)],
    index: usize,
    available: &FxHashSet<String>,
    previous: &mut usize,
) -> io::Result<Option<(String, ExprId)>> {
    let mut common = None;
    for &(method, list) in lists {
        let Some((left, right)) = cx.ir[list]
            .get(index)
            .and_then(|&expr| cx.ir[expr].as_assignment())
        else {
            return Ok(None);
        };
        let ExprKind::Field(field) = &cx.ir[left].kind else {
            return Ok(None);
        };
        let Some((field_index, key)) = declared_field(class, field, false) else {
            return Ok(None);
        };
        let variables = method.get(cx).variables;
        if *previous > field_index
            || !is_independent(
                cx,
                class,
                variables,
                right,
                field_index,
                InitializerContext::Instance { available },
            )?
        {
            return Ok(None);
        }
        *previous = field_index;
        if let Some((previous_key, previous_expr)) = &common {
            if previous_key != &key || !Expr::equals(cx, *previous_expr, right) {
                return Ok(None);
            }
        } else {
            common = Some((key, right));
        }
    }
    Ok(common)
}

fn process_dynamic_initializer(ir: &mut Ir, expr: ExprId) -> ExprId {
    if !matches!(ir[expr].kind, ExprKind::Function { .. }) {
        return unwrap_boxing_cast(ir, expr);
    }

    let mut inner = expr;
    while let ExprKind::Function { op, operands, .. } = &ir[inner].kind {
        if *op != FunctionType::Cast && op.simple_cast_type().is_none() {
            let count = operands.len();
            for index in 0..count {
                let operand = operand(ir, inner, index);
                let unboxed = unwrap_boxing_cast(ir, operand);
                let ExprKind::Function { operands, .. } = &mut ir[inner].kind else {
                    unreachable!();
                };
                operands[index] = unboxed;
            }
            return inner;
        }
        inner = operands[0];
    }
    expr
}

fn operand(ir: &Ir, func: ExprId, index: usize) -> ExprId {
    let ExprKind::Function { operands, .. } = &ir[func].kind else {
        unreachable!();
    };
    operands[index]
}

fn unwrap_boxing_cast(ir: &mut Ir, expr: ExprId) -> ExprId {
    if let ExprKind::Invocation(call) = &ir[expr].kind
        && call.is_unboxing_call()
        && let Some(inner) = call.instance
        && matches!(
            ir[inner].kind,
            ExprKind::Function {
                op: FunctionType::Cast,
                ..
            }
        )
    {
        let offsets = ir[expr].bytecode.clone();
        Expr::add_offsets(ir, inner, offsets.as_ref());
        return inner;
    }
    expr
}

#[derive(Clone, Copy)]
enum InitializerContext<'a> {
    Static {
        multiple: &'a FxHashSet<ArcStr>,
        remaining: &'a [ExprId],
    },
    Instance {
        available: &'a FxHashSet<String>,
    },
}

fn is_independent(
    cx: &mut Cx,
    class: &StructClass,
    variables: VarProcessorId,
    expr: ExprId,
    field_index: usize,
    context: InitializerContext<'_>,
) -> io::Result<bool> {
    for expr in Expr::all_exprents(&cx.ir, expr, true, true) {
        match &cx.ir[expr].kind {
            ExprKind::Variable(var) => {
                let pair = var.pair();
                let processor = &cx.ir[variables];
                if !processor.external_vars.contains(&pair)
                    && !processor
                        .names
                        .get(&pair)
                        .and_then(Option::as_deref)
                        .is_some_and(|name| name == "this" || name.ends_with(".this"))
                {
                    return Ok(false);
                }
            }
            ExprKind::Field(field) => {
                if let InitializerContext::Static { remaining, .. } = context
                    && remaining.iter().any(|&other| Expr::equals(cx, expr, other))
                {
                    return Ok(false);
                }
                let key = make_unique_key(&field.name, &field.descriptor.descriptor_string);
                let Some(referenced_index) = class.fields.index_of_key(key.as_str()) else {
                    continue;
                };
                match context {
                    InitializerContext::Static { multiple, .. } => {
                        if multiple.contains(&field.name) || !field.is_static() {
                            return Ok(false);
                        }
                        if referenced_index >= field_index {
                            force_qualified(&mut cx.ir, expr);
                        }
                    }
                    InitializerContext::Instance { available } => {
                        if !available.contains(&key) || referenced_index > field_index {
                            return Ok(false);
                        }
                    }
                }
            }
            ExprKind::New { .. } => qualify_lambda_fields(cx, class, expr, field_index)?,
            _ => {}
        }
    }
    Ok(true)
}

fn force_qualified(ir: &mut Ir, expr: ExprId) {
    let ExprKind::Field(field) = &mut ir[expr].kind else {
        unreachable!();
    };
    field.force_qualified = true;
}

fn qualify_lambda_fields(
    cx: &mut Cx,
    class: &StructClass,
    expr: ExprId,
    field_index: usize,
) -> io::Result<()> {
    if !class.fields[field_index].has_modifier(ACC_STATIC) {
        return Ok(());
    }
    let ExprKind::New {
        new_type,
        lambda: true,
        method_reference: false,
        ..
    } = &cx.ir[expr].kind
    else {
        return Ok(());
    };
    let (parent, key) = new_type
        .value
        .as_deref()
        .and_then(|name| cx.class_nodes.get(name))
        .and_then(|node| {
            Some((
                node.parent?,
                node.lambda.as_ref()?.content_method_key.clone(),
            ))
        })
        .ok_or_else(|| invalid("Missing initializer lambda metadata"))?;
    let method = MethodSlot::by_key(cx, parent, &key)
        .filter(|slot| slot.get(cx).root().is_some())
        .ok_or_else(|| invalid("Missing initializer lambda body"))?;

    // The Java set is keyed by expression identity. Every rewrite here is an
    // idempotent qualification of the existing field expression.
    let mut references = IndexSet::new();
    for list in cx.wrapper_expr_lists(method) {
        for &expr in &cx.ir[list] {
            references.extend(
                Expr::all_exprents(&cx.ir, expr, true, true)
                    .into_iter()
                    .filter(|&expr| {
                        matches!(cx.ir[expr].kind, ExprKind::Field(_) | ExprKind::New { .. })
                    }),
            );
        }
    }
    for expr in references {
        match &cx.ir[expr].kind {
            ExprKind::Field(field)
                if field.is_static() && field.classname.as_ref() == Some(&class.qualified_name) =>
            {
                let key = make_unique_key(&field.name, &field.descriptor.descriptor_string);
                if class
                    .fields
                    .index_of_key(key.as_str())
                    .is_some_and(|index| index > field_index)
                {
                    force_qualified(&mut cx.ir, expr);
                }
            }
            ExprKind::New { .. } => qualify_lambda_fields(cx, class, expr, field_index)?,
            _ => {}
        }
    }
    Ok(())
}

fn lift_constructor(cx: &mut Cx, class: &StructClass, constructors: &[(MethodSlot, StatId)]) {
    for &(method, root) in constructors {
        let Some(list) = first_data(&cx.ir, root) else {
            return;
        };
        for index in 0..cx.ir[list].len() {
            let expr = cx.ir[list][index];
            if let Some((left, right)) = cx.ir[expr].as_assignment()
                && Expr::variable(&cx.ir, right).is_some()
                && let ExprKind::Field(field) = &cx.ir[left].kind
                && field.classname.as_ref() == Some(&class.qualified_name)
                && class
                    .get_field(&field.name, &field.descriptor.descriptor_string)
                    .is_some_and(|field| field.has_modifier(ACC_FINAL))
            {
                continue;
            }
            if index > 0 && constructor_call(cx, method, class, expr, true) {
                cx.ir[list].remove(index);
                cx.ir[list].insert(0, expr);
            }
            break;
        }
    }
}

fn hide_empty_super(
    cx: &mut Cx,
    class: &StructClass,
    constructors: &[(MethodSlot, StatId)],
) -> io::Result<()> {
    for &(method, root) in constructors {
        let head = root.get_basic_head(&cx.ir);
        let Some(list) = cx.ir[head].exprents else {
            return Ok(());
        };
        let Some(&expr) = cx.ir[list].first() else {
            return Ok(());
        };
        if !constructor_call(cx, method, class, expr, false) {
            continue;
        }
        let ExprKind::Invocation(call) = &cx.ir[expr].kind else {
            unreachable!();
        };
        if super_parameters_are_synthetic(cx, call)? {
            cx.ir[list].remove(0);
        }
    }
    Ok(())
}

fn super_parameters_are_synthetic(cx: &Cx, call: &Invocation) -> io::Result<bool> {
    let mask = synthetic_parameters_mask(cx, call)?;
    for (index, param) in call.descriptor.params.iter().enumerate() {
        if let Some(mask) = &mask
            && mask
                .get(index)
                .ok_or_else(|| invalid("Incomplete synthetic constructor mask"))?
                .is_some()
        {
            continue;
        }
        if param.ty == CodeType::Object
            && param
                .value
                .as_deref()
                .and_then(|name| cx.class_nodes.get(name))
                .is_some_and(|node| {
                    node.kind == ClassKind::Anonymous || node.access & ACC_SYNTHETIC != 0
                })
        {
            break;
        }
        return Ok(false);
    }
    Ok(true)
}

fn invalid(message: impl Into<String>) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message.into())
}

/// An old compiler's constructor bridge ends with a synthetic marker class.
pub(super) fn hide_initializers(cx: &mut Cx, node: ClassNodeId) {
    let wrapper = cx.class_nodes[node]
        .wrapper
        .as_ref()
        .expect("Missing class wrapper");
    let hidden: Vec<_> = wrapper
        .methods
        .iter()
        .filter(|wrapper| wrapper.method.name == INIT_NAME && wrapper.method.is_synthetic())
        .filter_map(|wrapper| {
            let method = &wrapper.method;
            let descriptor = crate::types::MethodDescriptor::parse_descriptor(&method.descriptor);
            let parameter = descriptor.params.last()?;
            if parameter.ty != CodeType::Object {
                return None;
            }
            let marker = cx.class_nodes.get(parameter.value.as_deref()?)?;
            (marker.kind == ClassKind::Anonymous || marker.access & ACC_SYNTHETIC != 0)
                .then(|| make_unique_key(&method.name, &method.descriptor))
        })
        .collect();
    cx.class_nodes[node].hidden_members.extend(hidden);
}
