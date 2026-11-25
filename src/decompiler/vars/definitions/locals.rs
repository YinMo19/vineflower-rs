// Copyright 2000-2017 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Propagate local-variable table entries and the method's naming context.

use crate::code::code_constants::ACC_STATIC;
use crate::decompiler::{
    expr_processor::cast_type_name,
    exps::{Expr, ExprKind},
    ir::{ExprId, StatId, VarProcessorId},
    vars::var_version_pair::VarVersionPair as Version,
};
use crate::engine::{Cx, class_nodes::ClassKind};
use crate::structs::{StructMember, StructMethod, attr::LocalVariable};
use crate::types::{MethodDescriptor, VarType};
use crate::util::interpreter_util::make_unique_key;
use indexmap::IndexMap;
use rustc_hash::FxHashMap;
use std::{io, sync::Arc};

struct VarInfo {
    lvt: Option<Arc<LocalVariable>>,
    ty: Option<VarType>,
    cast: String,
}

impl VarInfo {
    fn new(cx: &mut Cx, lvt: Option<Arc<LocalVariable>>, ty: Option<VarType>) -> Self {
        let debug_type = lvt.as_ref().map(|entry| {
            entry.get_signature().map_or_else(
                || entry.get_var_type(),
                |signature| VarType::parse(signature),
            )
        });
        let cast = debug_type.as_ref().or(ty.as_ref()).map_or_else(
            || "this".to_owned(),
            |value| cast_type_name(cx, value, false),
        );
        Self { lvt, ty, cast }
    }
}

pub(super) fn propagate(
    cx: &mut Cx,
    root: StatId,
    owner: VarProcessorId,
    method: &StructMethod,
    descriptor: &MethodDescriptor,
) -> io::Result<()> {
    let mut types = IndexMap::<Version, VarInfo>::new();
    let is_static = method.has_modifier(ACC_STATIC);
    if let Some(table) = method.get_local_variable_attr() {
        for slot in (!is_static)
            .then_some(0)
            .into_iter()
            .chain(descriptor.parameter_slots(is_static).map(|(slot, _)| slot))
        {
            if let Some(lvt) = table.first_entry(slot) {
                types.insert(Version::new(slot, 0), VarInfo::new(cx, Some(lvt), None));
            }
        }
    }
    // StatementIterator, findTypes and applyTypes use the same occurrence
    // order. None of these passes adds or removes expressions.
    let expressions = root.all_exprents(&cx.ir);
    for &id in &expressions {
        let Some(var) = Expr::variable(&cx.ir, id) else {
            continue;
        };
        let pair = var.pair();
        let lvt = var.lvt.clone();
        let ty = match types.get(&pair) {
            None => Some(var.expr_type(cx)),
            Some(_) if var.definition => Some(var.expr_type(cx)),
            Some(old) if old.lvt.is_none() && lvt.is_some() => old.ty.clone(),
            Some(_) => continue,
        };
        types.insert(pair, VarInfo::new(cx, lvt, ty));
    }
    let type_names = types
        .iter()
        .map(|(&pair, info)| (pair, info.ty.as_ref(), info.cast.as_str()));
    let renames =
        method.with_variable_namer(&cx.options, |namer| namer.rename(method, type_names))?;
    inherit_names(cx, method, &expressions)?;

    let mut locals = FxHashMap::default();
    for (pair, info) in types {
        if !is_static && pair.var == 0 {
            continue;
        }
        let rename = renames.get(&pair);
        if let Some(name) = rename {
            cx.ir[owner].names.insert(pair, Some(name.clone()));
        }
        if let Some(mut lvt) = info.lvt {
            if let Some(name) = rename {
                lvt = Arc::new(lvt.rename(name.clone()));
            }
            cx.ir[owner].local_variables.insert(pair, lvt.clone());
            locals.insert(pair, lvt);
        }
    }
    if !locals.is_empty() {
        for id in expressions {
            if let Some(lvt) = Expr::variable(&cx.ir, id).and_then(|var| locals.get(&var.pair())) {
                Expr::set_local_variable(&mut cx.ir, id, lvt.clone());
            }
        }
    }
    Ok(())
}

fn inherit_names(cx: &Cx, method: &StructMethod, expressions: &[ExprId]) -> io::Result<()> {
    let mut children = Vec::<&Arc<StructMethod>>::new();
    for &id in expressions {
        if let ExprKind::New {
            anonymous: true,
            lambda,
            new_type,
            ..
        } = &cx.ir[id].kind
            && let Some(node) = cx.class_nodes.get(new_type.name())
        {
            if *lambda {
                if let Some(info) = &node.lambda
                    && !info.is_method_reference
                {
                    let child = node
                        .class
                        .get_method(&info.content_method_name, &info.content_method_descriptor)
                        .ok_or_else(|| {
                            io::Error::new(
                                io::ErrorKind::InvalidData,
                                "Missing lambda content method",
                            )
                        })?;
                    children.push(child);
                }
            } else {
                children.extend(node.class.methods.iter());
            }
        }
    }
    let key = make_unique_key(&method.name, &method.descriptor);
    let node = cx
        .class_nodes
        .get(&method.class_qualified_name)
        .ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                "Missing class node for local variable propagation",
            )
        })?;
    for &child in &node.nested {
        let child = &cx.class_nodes[child];
        if child.kind == ClassKind::Local && child.enclosing_method.as_deref() == Some(&key) {
            children.extend(child.class.methods.iter());
        }
    }
    if !children.is_empty() {
        let parent = method.with_variable_namer(&cx.options, |namer| namer.parent_context());
        let mut seen = rustc_hash::FxHashSet::default();
        for child in children {
            if seen.insert(Arc::as_ptr(child)) {
                child.with_variable_namer(&cx.options, |namer| namer.inherit(&parent));
            }
        }
    }
    Ok(())
}
