// Copyright 2000-2018 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Replace synthetic parameters and fields by variables from enclosing scopes.

use super::{ClassKind, ClassNodeId, Cx};
use crate::code::code_constants::INIT_NAME;
use crate::decompiler::{
    exps::{Expr, ExprKind, Field, InvocationFunction, Variable},
    ir::{ExprId, VarProcessorId},
    vars::{
        processor::VarNamesCollector, var_version_pair::VarVersionPair as Version,
        versions::FinalType,
    },
};
use crate::engine::{class_wrapper::MethodSlot, counter_container::VAR_COUNTER};
use crate::structs::attr::LocalVariable;
use crate::types::{MethodDescriptor, VarType};
use crate::util::{
    interpreter_util::{make_unique_key, make_unique_key3},
    jhash::JHashMap,
};
use arcstr::ArcStr;
use rustc_hash::FxHashMap;
use std::{io, sync::Arc};

fn enclosing_method(cx: &Cx, child: ClassNodeId) -> Option<MethodSlot> {
    let node = &cx.class_nodes[child];
    let key = node.enclosing_method.as_deref()?;
    let enclosing = node
        .parent
        .into_iter()
        .chain(
            node.enclosing_classes
                .iter()
                .filter_map(|name| cx.class_nodes.id(name)),
        )
        .find_map(|id| MethodSlot::by_key(cx, id, key));
    if enclosing.is_none() && node.kind != ClassKind::Member {
        log::warn!(
            "Couldn't find enclosing method {key} of {}",
            node.class.qualified_name
        );
    }
    enclosing
}

#[derive(Default)]
struct OuterVariable {
    name: Option<ArcStr>,
    ty: Option<VarType>,
    lvt: Option<Arc<LocalVariable>>,
}

#[derive(Default)]
struct Replacements {
    parameters: FxHashMap<i32, Version>,
    fields: FxHashMap<String, Version>,
}

pub fn insert_local_vars(cx: &mut Cx, parent: ClassNodeId, child: ClassNodeId) -> io::Result<()> {
    let enclosing = enclosing_method(cx, child);
    let class = Arc::clone(&cx.class_nodes[child].class);
    for (index, method) in class.methods.iter().enumerate() {
        let slot = MethodSlot { node: child, index };
        if !matches!(slot.get(cx).body, Ok(Some(_))) {
            continue;
        }
        if let Some(outer) = enclosing {
            let parent_names = outer
                .get(cx)
                .method
                .with_variable_namer(&cx.options, |namer| namer.parent_context());
            method.with_variable_namer(&cx.options, |namer| namer.inherit(&parent_names));
        }
        let mut replacements = Replacements::default();
        let mut vars = JHashMap::new();
        if let Some(mask) = slot.get(cx).synthetic_parameters.clone() {
            let descriptor = MethodDescriptor::parse_descriptor(&method.descriptor);
            for ((index, _), captured) in descriptor.parameter_slots(false).zip(mask) {
                if let Some(pair) = captured {
                    let fresh = allocate(cx, slot, child, parent, enclosing, pair, &mut vars)?;
                    replacements.parameters.insert(index, fresh);
                }
            }
        }
        let mut owner = Some(child);
        while let Some(id) = owner {
            let node = &cx.class_nodes[id];
            owner = node.parent;
            if node.fields_to_vars.is_empty() {
                continue;
            }
            let enclosing = enclosing_method(cx, id);
            let parent = owner.expect("Captured field without an enclosing class");
            let fields: Vec<_> = node
                .fields_to_vars
                .iter()
                .map(|(field, &pair)| (field.clone(), pair))
                .collect();
            for (field, pair) in fields {
                let fresh = allocate(cx, slot, id, parent, enclosing, pair, &mut vars)?;
                let node = &mut cx.class_nodes[id];
                replacements
                    .fields
                    .insert(make_unique_key(&node.class.qualified_name, &field), fresh);
                if id == child && node.class.fields.get_with_key(&field).is_some() {
                    node.hidden_members.insert(field);
                }
            }
        }
        let variables = slot.get(cx).variables;
        let outer_names = &mut slot.get_mut(cx).outer_var_names;
        let mut collector = VarNamesCollector::default();
        collector.used.extend(
            vars.values()
                .map(|v| v.name.clone())
                .filter(|name| !outer_names.contains(name)),
        );
        outer_names.extend(collector.used.iter().cloned());
        let processor = &mut cx.ir[variables];
        processor.refresh_names(&mut collector);
        for (&pair, binding) in vars.iter() {
            processor.inherit_name(pair, binding.name.clone());
            if let Some(ty) = &binding.ty {
                processor.versions.lower.insert(pair, ty.clone());
            }
            if let Some(lvt) = &binding.lvt {
                processor.local_variables.insert(pair, lvt.clone());
            }
        }
        replacements.apply(cx, slot, method.name == INIT_NAME);
    }
    Ok(())
}

fn allocate(
    cx: &mut Cx,
    slot: MethodSlot,
    owner: ClassNodeId,
    parent: ClassNodeId,
    enclosing: Option<MethodSlot>,
    captured: Version,
    vars: &mut JHashMap<Version, OuterVariable>,
) -> io::Result<Version> {
    let variables = slot.get(cx).variables;
    let counter = &mut slot
        .get_mut(cx)
        .body
        .as_mut()
        .unwrap()
        .as_mut()
        .unwrap()
        .counters;
    let fresh = Version::new(counter.get_counter_and_increment(VAR_COUNTER), 0);
    let mut binding = OuterVariable::default();
    if cx.class_nodes[owner].kind != ClassKind::Member {
        let enclosing = enclosing.ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                "Missing enclosing method for captured variable",
            )
        })?;
        let outer = enclosing.get(cx).variables;
        let processor = &mut cx.ir[outer];
        binding.name = processor.names.get(&captured).cloned().flatten();
        binding.ty = processor.versions.lower.get(&captured).cloned();
        binding.lvt = processor.local_variables.get(&captured).cloned();
        if processor.versions.initialized {
            processor
                .versions
                .final_vars
                .insert(captured, FinalType::ExplicitFinal);
        }
    }
    if captured.var == -1
        || binding.name.as_deref() == Some("this")
        || binding.lvt.as_ref().is_some_and(|v| v.get_name() == "this")
    {
        let parent = &cx.class_nodes[parent];
        let name: ArcStr = parent.simple_name.as_ref().map_or_else(
            || arcstr::literal!("<VAR_NAMELESS_ENCLOSURE>"),
            |name| format!("{name}.this").into(),
        );
        binding.lvt = binding.lvt.map(|v| Arc::new(v.rename(name.clone())));
        binding.name = Some(name);
        cx.ir[variables]
            .this_vars
            .insert(fresh, parent.class.qualified_name.clone());
    }
    vars.insert(fresh, binding);
    Ok(fresh)
}

impl Replacements {
    fn field(&self, field: &Field) -> Option<Version> {
        let key = make_unique_key3(
            field.classname.as_deref().unwrap_or("null"),
            &field.name,
            &field.descriptor.descriptor_string,
        );
        self.fields.get(&key).copied()
    }

    fn apply(&self, cx: &mut Cx, slot: MethodSlot, constructor: bool) {
        let variables = slot.get(cx).variables;
        for list in cx.wrapper_expr_lists(slot) {
            let mut i = 0;
            while i < cx.ir[list].len() {
                let expr = cx.ir[list][i];
                if self.remove(cx, slot.node, expr, constructor) {
                    cx.ir[list].remove(i);
                    continue;
                }
                if let Some(new) = self.replace(cx, variables, expr) {
                    cx.ir[list][i] = new;
                }
                i += 1;
            }
        }
    }

    fn remove(&self, cx: &mut Cx, child: ClassNodeId, expr: ExprId, constructor: bool) -> bool {
        match &cx.ir[expr].kind {
            ExprKind::Assignment { left, .. } => matches!(&cx.ir[*left].kind,
                ExprKind::Field(f) if f.classname.as_ref() == Some(&cx.class_nodes[child].class.qualified_name)
                    && self.field(f).is_some()),
            ExprKind::Invocation(inv) if constructor => {
                if cx.class_nodes[child].kind == ClassKind::Anonymous
                    && inv.function == InvocationFunction::Init
                {
                    cx.class_nodes[child].super_invocation = Some(expr);
                    return true;
                }
                inv.is_static
                    && inv.classname.as_deref() == Some("java/util/Objects")
                    && inv.name == "requireNonNull"
                    && inv.string_descriptor() == "(Ljava/lang/Object;)Ljava/lang/Object;"
                    && inv
                        .parameters
                        .first()
                        .and_then(|&id| Expr::variable(&cx.ir, id))
                        .is_some_and(|v| self.parameters.contains_key(&v.index))
            }
            _ => false,
        }
    }

    fn replace(&self, cx: &mut Cx, variables: VarProcessorId, expr: ExprId) -> Option<ExprId> {
        let pair = match &cx.ir[expr].kind {
            ExprKind::Variable(v) => self.parameters.get(&v.index).copied(),
            ExprKind::Field(f) => self.field(f),
            _ => None,
        };
        if let Some(pair) = pair {
            let processor = &mut cx.ir[variables];
            processor.external_vars.insert(pair);
            let var = Variable::in_method(
                pair.var,
                processor.versions.lower.get(&pair).cloned(),
                variables,
            );
            let lvt = processor.local_variables.get(&pair).cloned();
            let bytecode = cx.ir[expr].bytecode.clone();
            let expr = Expr::new_ambient(cx, ExprKind::Variable(var), bytecode);
            if let Some(lvt) = lvt {
                Expr::set_local_variable(&mut cx.ir, expr, lvt);
            }
            return Some(expr);
        }

        loop {
            let children: Vec<_> = Expr::children(&cx.ir, expr).collect();
            let (old, new) = children
                .into_iter()
                .find_map(|old| self.replace(cx, variables, old).map(|new| (old, new)))?;
            Expr::replace(&mut cx.ir, expr, old, new);
        }
    }
}
