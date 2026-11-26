// Copyright 2000-2024 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! `InvocationExprent.getInferredExprType`, including qualifier and argument constraints.

use std::{io, sync::Arc};

use super::bounds::Mappings;
use super::{
    Inference, filtered_names, gather_generics, generic_arguments, instance_of, invalid,
    invocation, name_type,
};
use crate::code::code_constants::{ACC_ENUM, ACC_PRIVATE, ACC_PROTECTED, ACC_PUBLIC, ACC_STATIC};
use crate::decompiler::exps::{Expr, ExprKind, Invocation, InvocationFunction};
use crate::decompiler::ir::ExprId;
use crate::engine::Cx;
use crate::engine::class_nodes::{ClassKind, ClassNode, ClassNodeId};
use crate::structs::{StructClass, StructMember, StructMethod};
use crate::types::{CodeType, GenericType, GenericsMap, TypeFamily, VarType};
use crate::util::jhash::{JHashMap, JHashSet};

impl Inference<'_> {
    pub(super) fn infer_invocation(
        &mut self,
        expr: ExprId,
        upper: Option<&VarType>,
    ) -> io::Result<VarType> {
        let method = Invocation::resolve_description(self.cx, expr);
        let (receiver, klass, erased, constructor, unboxing, descriptor) = {
            let call = invocation(&self.cx.ir, expr);
            (
                call.instance,
                call.classname.clone(),
                call.descriptor.ret.clone(),
                call.function == InvocationFunction::Init,
                call.is_unboxing_call(),
                call.descriptor.clone(),
            )
        };
        let state = self.invocation_state(expr);
        state.arguments.clear();
        state.mappings.clear();
        state.remapped_instance = None;
        let is_instance = state.is_invocation_instance;
        let force = state.force_qualification;

        let owner = klass
            .as_deref()
            .and_then(|class| self.cx.classes().get_class(class));
        if unboxing && let (Some(upper), Some(instance)) = (upper, receiver) {
            let child = self.skip_cast(instance);
            if child != instance {
                let inferred = self.infer(child, Some(upper))?;
                if inferred.unboxing_type().as_ref() != Some(upper)
                    && (inferred.type_family == TypeFamily::Object || inferred.is_generic())
                {
                    self.invocation_state(expr).keep_unboxing_cast = true;
                }
            }
        }
        let (Some(method), Some(owner)) = (method, owner) else {
            return Ok(erased);
        };
        let method_signature = method.signature();
        let class_signature = owner.signature();
        let generic_new = constructor && class_signature.is_some();
        let (formals, declared_ret) = if generic_new {
            let signature = class_signature.as_ref().unwrap();
            (&signature.fparameters, &signature.generic_type)
        } else if let Some(signature) = &method_signature {
            (&signature.type_parameters, &signature.return_type)
        } else {
            return Ok(erased);
        };

        let values = std::mem::take(&mut self.invocation_state(expr).mappings);
        let mut mapping = Mappings::new(
            self.cx,
            &owner,
            method_signature.as_deref(),
            self.named_generics(),
            values,
        );
        let inherited = if owner.qualified_name != method.class_qualified_name {
            owner
                .get_all_generics(self.cx)
                .get(&method.class_qualified_name)
                .cloned()
        } else {
            None
        };
        let empty = GenericsMap::new();
        let inherited = inherited.as_deref().unwrap_or(&empty);
        for (from, to) in inherited.iter() {
            let to = to
                .as_ref()
                .ok_or_else(|| invalid("Null inherited generic mapping"))?;
            if to.ty == CodeType::Genvar {
                if let Some(bound) = mapping.bounds.get(to).cloned()
                    && !mapping.bounds.contains_key(from)
                {
                    mapping.bounds.insert(from.clone(), bound);
                }
            } else if !mapping.bounds.contains_key(from) {
                mapping.values.insert(from.clone(), Some(to.clone()));
            }
        }

        let mut upper_mappings = upper_mappings(self.cx, &mut mapping, upper, declared_ret);
        let dummy = GenericType::dummy_var();
        for formal in formals.iter().chain(
            class_signature
                .as_ref()
                .into_iter()
                .flat_map(|sig| &sig.fparameters),
        ) {
            let formal = name_type(formal);
            if !upper_mappings.contains_key(&formal) {
                upper_mappings.insert(formal, Some(dummy.clone()));
            }
        }

        let mut receiver_type = None;
        if let Some(receiver) = receiver
            && !constructor
        {
            self.mark_instance(receiver);
            let receiver_bound = match &class_signature {
                Some(signature) => signature.generic_type.remap_for_inference(&upper_mappings),
                None => upper.cloned(),
            };
            let mut actual = self.infer(self.skip_cast(receiver), receiver_bound.as_ref())?;
            if actual.ty == CodeType::Genvar
                && let Some(named) = mapping.named.get(&actual).and_then(|bounds| bounds.first())
            {
                actual = named.clone();
            }
            if actual.is_generic()
                && actual.ty != CodeType::Genvar
                && let Some(class) = actual
                    .value
                    .as_deref()
                    .and_then(|name| self.cx.classes().get_class(name))
                && let Some(signature) = class.signature()
            {
                let mut temporary = GenericsMap::new();
                signature
                    .generic_type
                    .map_gen_vars_to(self.cx, &actual, &mut temporary);
                for (from, to) in temporary.iter() {
                    if !formals
                        .iter()
                        .any(|formal| Some(formal.as_str()) == from.value.as_deref())
                    {
                        mapping.process(self.cx, from.clone(), to.clone());
                    }
                }
            }
            receiver_type = Some(actual);
        }

        if upper.is_none()
            && generic_new
            && let Some(current) = self.current_class()
        {
            if Arc::ptr_eq(&owner, &current) {
                for variable in class_signature
                    .as_ref()
                    .unwrap()
                    .generic_type
                    .get_all_generic_vars()
                {
                    mapping.values.insert(variable.clone(), Some(variable));
                }
            } else if let Some(inherited) =
                current.get_all_generics(self.cx).get(&owner.qualified_name)
            {
                for (from, to) in inherited.iter() {
                    mapping.values.insert(from.clone(), to.clone());
                }
            }
        }

        if !is_instance {
            for (formal, value) in upper_mappings.iter() {
                if !mapping.values.contains_key(formal)
                    && is_formal_mapping(formal, value.as_ref(), formals, &dummy)
                {
                    mapping.values.insert(formal.clone(), value.clone());
                }
            }
        }

        let mut parameter_generics = JHashSet::new();
        let arguments = invocation(&self.cx.ir, expr).parameters.clone();
        if let Some(signature) = &method_signature
            && !arguments.is_empty()
        {
            let slots = invocation_parameter_indices(
                self.cx,
                &owner,
                descriptor.as_str(),
                arguments.len(),
                constructor,
            )?;
            let common = self.common_class_generics(&owner, &method);
            for (index, formal) in slots.zip(&signature.parameter_types) {
                if !formal.is_generic() {
                    continue;
                }
                let argument = arguments[index];
                let excluded = self.excluded_lambda_generics(argument, formal)?;
                let mut combined = JHashMap::copy_of(&mapping.values);
                for (key, value) in upper_mappings.iter() {
                    if !combined.contains_key(key) {
                        combined.insert(key.clone(), value.clone());
                    }
                }
                let viewed = formal
                    .remap_for_inference(inherited)
                    .ok_or_else(|| invalid("Null inherited parameter type"))?;
                let argument_bound = viewed.remap_for_inference(&combined);
                let mut actual = self.infer(self.skip_cast(argument), argument_bound.as_ref())?;

                if argument_bound.is_none()
                    && actual != VarType::VARTYPE_NULL
                    && combined.get(formal) == Some(&None)
                    && let Some(receiver) = receiver_type.as_ref().filter(|ty| ty.is_generic_type())
                    && let Some(base) = receiver.find_base_type(self.cx)
                {
                    combined.insert(formal.clone(), Some(actual.clone()));
                    let remapped = base
                        .remap_for_inference(inherited)
                        .and_then(|ty| ty.remap_for_inference(&combined));
                    self.invocation_state(expr).remapped_instance = remapped;
                }

                // Java resolves both raw names before checking whether the
                // actual argument can supply type parameters.
                let formal_class = formal
                    .value
                    .as_deref()
                    .and_then(|name| self.cx.classes().get_class(name));
                let actual_class = if actual.ty == CodeType::Genvar {
                    None
                } else {
                    actual
                        .value
                        .as_deref()
                        .and_then(|name| self.cx.classes().get_class(name))
                };
                if formal_class.is_some() && actual_class.is_some() {
                    if formal.value != actual.value {
                        actual = VarType::get_generic_super_type(self.cx, &actual, formal);
                    }
                    if actual.is_generic() {
                        let mut temporary = GenericsMap::new();
                        formal.map_gen_vars_to(self.cx, &actual, &mut temporary);
                        VarType::clean_lowered_generic_types(
                            &mut temporary,
                            formal,
                            &actual,
                            Some(&common),
                        );
                        for (from, to) in temporary.iter() {
                            if !excluded.contains(from) {
                                parameter_generics.insert(from.clone());
                            }
                            if !mapping.process(self.cx, from.clone(), to.clone())
                                && to.as_ref().is_some_and(|ty| !ty.is_generic())
                                && mapping
                                    .values
                                    .get(from)
                                    .and_then(Option::as_ref)
                                    .is_some_and(|ty| !ty.is_generic())
                            {
                                mapping.put(self.cx, from.clone(), to.clone());
                            }
                        }
                    }
                } else if formal.ty == CodeType::Genvar
                    && *formal != actual
                    && actual.array_dim >= formal.array_dim
                {
                    let mut formal = formal.clone();
                    if formal.array_dim > 0 {
                        actual = actual.resize_array_dim(actual.array_dim - formal.array_dim);
                        formal = formal.resize_array_dim(0);
                    }
                    if !excluded.contains(&formal) {
                        parameter_generics.insert(formal.clone());
                    }
                    mapping.process(self.cx, formal, Some(actual));
                }
            }
        }

        for (formal, value) in upper_mappings.iter() {
            if !is_formal_mapping(formal, value.as_ref(), formals, &dummy) {
                continue;
            }
            if let (Some(current), Some(value)) =
                (mapping.values.get(formal).and_then(Option::as_ref), value)
                && !current.is_generic()
                && !value.is_generic()
                && !instance_of(self.cx, current, value)
            {
                continue;
            }
            mapping.process(self.cx, formal.clone(), value.clone());
        }

        let mut inferred = None;
        let mut generic_args = Vec::new();
        if !mapping.values.is_empty() {
            let ret = declared_ret
                .remap_for_inference(inherited)
                .ok_or_else(|| invalid("Null inherited return type"))?;
            let returns_formal = ret.is_generic()
                && ret.get_all_generic_vars().iter().any(|var| {
                    formals
                        .iter()
                        .any(|name| Some(name.as_str()) == var.value.as_deref())
                });
            let mut result = ret.remap_for_inference(&mapping.values);
            if result.is_none()
                && let Some(bound) = mapping
                    .bounds
                    .get(declared_ret)
                    .and_then(|bounds| bounds.first())
            {
                result = bound.remap_for_inference(&mapping.values);
            }
            if returns_formal && (!constructor || generic_new) {
                let missing = parameter_generics.is_empty()
                    || formals
                        .iter()
                        .any(|name| !parameter_generics.contains(&name_type(name)));
                let suppress = (!missing || !is_instance)
                    && result.as_ref().is_some_and(|result| {
                        upper.is_none_or(|upper| {
                            !result.is_generic() || instance_of(self.cx, result, upper)
                        })
                    })
                    && !force;
                if !suppress || self.cx.options.explicit_generics {
                    generic_args = generic_arguments(formals, &mapping.values);
                } else if generic_new {
                    generic_args.push(dummy);
                }
            }
            if let Some(result) = result
                && !result.same_generic_reference(declared_ret)
                && (!result.is_generic()
                    || !result.has_unknown_generic_type(&filtered_names(&mapping.named)))
            {
                inferred = Some(result);
            }
        }
        let state = self.invocation_state(expr);
        state.arguments = generic_args;
        state.mappings = mapping.values;
        if declared_ret.is_generic() && declared_ret.get_all_generic_vars().is_empty() {
            return Ok(inferred.unwrap_or_else(|| declared_ret.clone()));
        }
        Ok(inferred.unwrap_or(erased))
    }

    fn common_class_generics(
        &self,
        owner: &StructClass,
        method: &StructMethod,
    ) -> JHashSet<VarType> {
        let mut names = JHashSet::new();
        if method.has_modifier(ACC_STATIC)
            || self
                .cx
                .writing_method()
                .is_none_or(|wrapper| wrapper.method.has_modifier(ACC_STATIC))
        {
            return names;
        }
        let nodes = &self.cx.class_nodes;
        let parent = |&id: &ClassNodeId| {
            let node = &nodes[id];
            (node.access & ACC_STATIC == 0)
                .then_some(node.parent)
                .flatten()
        };
        let parents: Vec<_> = std::iter::successors(self.cx.current_node(), parent).collect();
        for id in std::iter::successors(nodes.id(&owner.qualified_name), parent) {
            if parents.contains(&id)
                && let Some(signature) = nodes[id].class.signature()
            {
                names.extend(signature.fparameters.iter().map(|name| name_type(name)));
            }
        }
        names
    }

    fn excluded_lambda_generics(
        &self,
        expr: ExprId,
        formal: &VarType,
    ) -> io::Result<JHashSet<VarType>> {
        let mut excluded = JHashSet::new();
        let ExprKind::New {
            lambda: true,
            new_type,
            ..
        } = &self.cx.ir[expr].kind
        else {
            return Ok(excluded);
        };
        let info = new_type
            .value
            .as_deref()
            .and_then(|name| self.cx.class_nodes.get(name))
            .and_then(|node| node.lambda.as_ref())
            .ok_or_else(|| invalid("Lambda parameter has no class node metadata"))?;
        if info.is_method_reference
            && let Some(content) = self.cx.classes().get_class(&info.content_class_name)
        {
            let current = self.current_class();
            let mut count = 0;
            for method in &content.methods {
                if can_access(self.cx, current.as_deref(), method)?
                    && method.name == info.content_method_name
                {
                    count += 1;
                }
            }
            if count <= 1 {
                return Ok(excluded);
            }
        }

        let lambda = Expr::expr_type(self.cx, expr);
        let Some(interface) = lambda
            .value
            .as_deref()
            .and_then(|name| self.cx.classes().get_class(name))
        else {
            return Ok(excluded);
        };
        // During ClassWrapper.init, only the active method's sequence is expanded.
        let Some(method) = interface.methods.iter().find(|method| {
            !method.has_modifier(ACC_STATIC)
                && self
                    .expanded_method
                    .as_ref()
                    .is_none_or(|active| !Arc::ptr_eq(method, active))
        }) else {
            return Ok(excluded);
        };
        let (Some(class_signature), Some(method_signature)) =
            (interface.signature(), method.signature())
        else {
            return Ok(excluded);
        };
        let mut variables = GenericsMap::new();
        class_signature
            .generic_type
            .map_gen_vars_to(self.cx, formal, &mut variables);
        for ty in &method_signature.parameter_types {
            if ty.is_generic() {
                for var in ty.get_all_generic_vars() {
                    if let Some(Some(mapped)) = variables.get(&var)
                        && mapped.is_generic()
                    {
                        excluded.extend(mapped.get_all_generic_vars());
                    }
                }
            }
        }
        Ok(excluded)
    }
}

fn can_access(cx: &Cx, current: Option<&StructClass>, method: &StructMethod) -> io::Result<bool> {
    if method.has_modifier(ACC_PUBLIC) {
        return Ok(true);
    }
    let current = current.ok_or_else(|| invalid("No current class for method accessibility"))?;
    let owner = &method.class_qualified_name;
    let class = &current.qualified_name;
    if method.has_modifier(ACC_PRIVATE) {
        return Ok(class == owner);
    }
    let same_package =
        class.rsplit_once('/').map(|(p, _)| p) == owner.rsplit_once('/').map(|(p, _)| p);
    Ok(same_package
        || (method.has_modifier(ACC_PROTECTED) && cx.classes().instance_of(class, owner)))
}

fn invocation_parameter_indices(
    cx: &Cx,
    owner: &StructClass,
    descriptor: &str,
    count: usize,
    constructor: bool,
) -> io::Result<std::ops::Range<usize>> {
    let mut start = 0;
    let Some(node_id) = cx.class_nodes.id(&owner.qualified_name) else {
        return Ok(start..count);
    };
    let node = &cx.class_nodes[node_id];
    if constructor {
        if let Some(wrapper_owner) = cx.class_nodes.wrapper_owner(node_id)
            && cx.class_nodes[wrapper_owner].wrapper.is_some()
        {
            // Constructor wrappers have no synthetic mask until the later
            // NestedClassProcessor pass allocates it.
            if cx.class_nodes[wrapper_owner]
                .class
                .get_method("<init>", descriptor)
                .is_none()
                && !cx.options.ignore_invalid_bytecode
            {
                return Err(invalid(
                    "Constructor missing from the published class wrapper",
                ));
            }
        } else if count > 0 && node.kind == ClassKind::Member && !is_static_member(node) {
            start = 1;
        }
        if owner.has_modifier(ACC_ENUM) {
            start = 2;
        }
    } else if !node.enclosing_classes.is_empty() && node.access & ACC_STATIC == 0 {
        start = 1;
    }
    Ok(start..count)
}

fn is_static_member(node: &ClassNode) -> bool {
    node.class.has_modifier(ACC_STATIC)
        || node
            .class
            .attributes
            .inner_classes
            .as_ref()
            .and_then(|entries| {
                entries
                    .entries
                    .iter()
                    .find(|entry| entry.inner_name == node.class.qualified_name)
            })
            .is_some_and(|entry| entry.access_flags & ACC_STATIC != 0)
}

fn is_formal_mapping(
    formal: &VarType,
    value: Option<&VarType>,
    names: &[String],
    dummy: &VarType,
) -> bool {
    value != Some(dummy)
        && names
            .iter()
            .any(|name| Some(name.as_str()) == formal.value.as_deref())
}

fn upper_mappings(
    cx: &Cx,
    mapping: &mut Mappings,
    upper: Option<&VarType>,
    ret: &VarType,
) -> GenericsMap {
    let mut output = GenericsMap::new();
    let Some(upper) = upper.filter(|upper| {
        **upper != VarType::VARTYPE_OBJECT
            && (upper.ty != CodeType::Genvar || mapping.named.contains_key(upper))
    }) else {
        return output;
    };
    let (mut view, mut target) = (upper.clone(), ret.clone());
    if view.ty != CodeType::Genvar && target.ty != CodeType::Genvar && view.value != target.value {
        if instance_of(cx, &view, &target) {
            view = VarType::get_generic_super_type(cx, &view, &target);
        } else {
            target = VarType::get_generic_super_type(cx, &target, &view);
        }
    }
    if target.ty == CodeType::Genvar
        && (upper.type_family == TypeFamily::Object || upper.is_generic())
    {
        output.insert(
            target.resize_array_dim(0),
            Some(upper.resize_array_dim((upper.array_dim - target.array_dim).max(0))),
        );
    } else {
        let mut gathered = GenericsMap::new();
        gather_generics(cx, Some(&view), &target, &mut gathered);
        for (from, to) in gathered.iter() {
            let Some(to) = to else { continue };
            if mapping.values.contains_key(from) {
                continue;
            }
            if to.ty == CodeType::Genvar {
                let Some(named) = mapping.named.get(to) else {
                    continue;
                };
                if mapping.named.contains_key(from)
                    && mapping
                        .bounds
                        .get(from)
                        .is_some_and(|bounds| bounds.contains(&VarType::VARTYPE_OBJECT))
                    && !mapping.bounds.contains_key(to)
                    && !named.contains(from)
                {
                    continue;
                }
            }
            if mapping.in_bounds(cx, from, Some(to)) {
                output.insert(from.clone(), Some(to.clone()));
            }
        }
    }
    output
}
