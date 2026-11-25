// Copyright 2000-2024 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Generic object allocations and LambdaMetafactory expressions.

use std::io;

use super::{
    AllocationGenerics, Inference, filtered_names, gather_generics, generic_arguments, instance_of,
    invalid, invocation,
};
use crate::code::code_constants::INIT_NAME;
use crate::decompiler::exps::{ExitType, Expr, ExprKind};
use crate::decompiler::ir::ExprId;
use crate::decompiler::stats::StatementKind;
use crate::decompiler::vars::var_version_pair::VarVersionPair;
use crate::engine::class_nodes::{ClassNodeId, LambdaInformation};
use crate::structs::consts::PooledConstant;
use crate::types::{
    CodeType, GenericMethodDescriptor, GenericType, GenericsMap, MethodDescriptor, VarType,
};

impl Inference<'_> {
    pub(crate) fn has_overloaded_method_reference(&self, expr: ExprId) -> bool {
        let ExprKind::New {
            new_type,
            lambda: true,
            method_reference: true,
            ..
        } = &self.cx.ir[expr].kind
        else {
            return false;
        };
        let Some(info) = new_type
            .value
            .as_deref()
            .and_then(|name| self.cx.class_nodes.get(name))
            .and_then(|node| node.lambda.as_ref())
        else {
            return false;
        };
        let Some(content) = self.cx.class_nodes.get(&info.content_class_name) else {
            return false;
        };
        content
            .class
            .methods
            .iter()
            .filter(|method| method.name == info.content_method_name)
            .nth(1)
            .is_some()
    }

    pub(super) fn infer_allocation(
        &mut self,
        expr: ExprId,
        upper: Option<&VarType>,
    ) -> io::Result<VarType> {
        let ExprKind::New {
            new_type,
            lambda,
            anonymous,
            constructor,
            array_elements,
            ..
        } = &self.cx.ir[expr].kind
        else {
            unreachable!()
        };
        let (new_type, lambda, anonymous, constructor) =
            (new_type.clone(), *lambda, *anonymous, *constructor);
        let elements = array_elements.clone();
        if let ExprKind::New {
            generics: Some(state),
            ..
        } = &mut self.cx.ir[expr].kind
        {
            state.arguments.clear();
        }

        if lambda {
            if let Some(ty) = self.infer_lambda(expr, &new_type, constructor, upper)? {
                return Ok(ty);
            }
        } else if new_type.ty == CodeType::Object {
            let signature = new_type
                .value
                .as_deref()
                .and_then(|name| self.cx.classes().get_class(name))
                .and_then(|class| class.signature());
            if let Some(signature) = signature {
                if anonymous {
                    if signature.superclass == VarType::VARTYPE_OBJECT
                        && let Some(interface) = signature.superinterfaces.first()
                    {
                        return Ok(interface.clone());
                    }
                    return Ok(signature.superclass.clone());
                }
                if new_type.array_dim == 0 && !signature.fparameters.is_empty() {
                    if let Some(constructor) = constructor {
                        let ty = self.infer(constructor, upper)?;
                        if ty.ty != CodeType::Void {
                            return Ok(ty);
                        }
                    } else {
                        let mut map = GenericsMap::new();
                        gather_generics(self.cx, upper, &signature.generic_type, &mut map);
                        self.allocation_state(expr).arguments =
                            generic_arguments(&signature.fparameters, &map);
                        if let Some(inferred) = signature.generic_type.remap_for_inference(&map)
                            && !inferred.same_generic_reference(&signature.generic_type)
                        {
                            return Ok(inferred);
                        }
                    }
                }
            } else if new_type.array_dim > 0
                && new_type.value == VarType::VARTYPE_OBJECT.value
                && let Some((&first, rest)) = elements.split_first()
            {
                let first = self.infer(first, None)?;
                if first.ty == CodeType::Genvar {
                    let mut matches = true;
                    for &element in rest {
                        if self.infer(element, None)? != first {
                            matches = false;
                            break;
                        }
                    }
                    if matches {
                        return Ok(first.resize_array_dim(new_type.array_dim));
                    }
                }
            }
        }
        Ok(Expr::expr_type(self.cx, expr))
    }

    fn allocation_state(&mut self, expr: ExprId) -> &mut AllocationGenerics {
        let ExprKind::New { generics, .. } = &mut self.cx.ir[expr].kind else {
            unreachable!()
        };
        generics.get_or_insert_with(Default::default)
    }

    fn infer_lambda(
        &mut self,
        expr: ExprId,
        new_type: &VarType,
        constructor: Option<ExprId>,
        upper: Option<&VarType>,
    ) -> io::Result<Option<VarType>> {
        let Some(node_id) = new_type
            .value
            .as_deref()
            .and_then(|name| self.cx.class_nodes.id(name))
        else {
            return Ok(None);
        };
        let node = &self.cx.class_nodes[node_id];
        let class_type = node
            .anonymous_type
            .clone()
            .ok_or_else(|| invalid("Lambda has no interface type"))?;
        let info = node
            .lambda
            .clone()
            .ok_or_else(|| invalid("Lambda has no method metadata"))?;
        let ExprKind::New {
            method_reference, ..
        } = self.cx.ir[expr].kind
        else {
            unreachable!()
        };

        let interface = class_type
            .value
            .as_deref()
            .and_then(|name| self.cx.classes().get_class(name));
        let method_class = self.cx.classes().get_class(&info.content_class_name);
        let class_signature = interface.as_ref().and_then(|class| class.signature());
        let (Some(interface), Some(method_class), Some(signature)) =
            (interface, method_class, class_signature)
        else {
            self.allocation_state(expr).inferred_lambda_type = Some(class_type);
            return Ok(None);
        };
        let sam_descriptor = if let Some(constructor) = constructor {
            let call = invocation(&self.cx.ir, constructor);
            match call
                .bootstrap_arguments
                .as_ref()
                .and_then(|args| args.first())
            {
                Some(Some(PooledConstant::Primitive(descriptor))) => {
                    descriptor.get_string().as_str()
                }
                _ => return Err(invalid("Missing LambdaMetafactory SAM descriptor")),
            }
        } else {
            ""
        };
        let (Some(sam), Some(method)) = (
            interface.get_method(&info.method_name, sam_descriptor),
            method_class.get_method(&info.content_method_name, &info.content_method_descriptor),
        ) else {
            return Ok(None);
        };
        let Some(sam_signature) = sam.signature() else {
            return Ok(None);
        };
        let method_signature = method.signature();
        let descriptor = MethodDescriptor::parse_descriptor(&info.method_descriptor);
        let ret = &signature.generic_type;
        let mut mappings = GenericsMap::new();
        gather_generics(self.cx, upper, ret, &mut mappings);

        let mut instance_map = GenericsMap::new();
        let method_class_signature = method_class.signature();
        if method_reference && let Some(signature) = &method_class_signature {
            if let Some(instance) = constructor.and_then(|id| invocation(&self.cx.ir, id).instance)
            {
                let instance = self.infer(instance, None)?;
                if instance.is_generic() {
                    signature
                        .generic_type
                        .map_gen_vars_to(self.cx, &instance, &mut instance_map);
                }
            } else if let Some(method_signature) = &method_signature {
                for (index, ty) in method_signature.parameter_types.iter().enumerate() {
                    let parameter = sam_signature.parameter_types.get(index).ok_or_else(|| {
                        invalid("Lambda method reference has unmatched SAM parameter")
                    })?;
                    if ty.ty == CodeType::Genvar
                        && parameter.ty == CodeType::Genvar
                        && let Some(mapped) = mappings.get(parameter)
                    {
                        instance_map.insert(ty.clone(), mapped.clone());
                    }
                }
            }
        }

        let parameter_types = method_signature
            .as_ref()
            .map_or(&descriptor.params, |sig| &sig.parameter_types);
        for (ty, parameter) in parameter_types.iter().zip(&sam_signature.parameter_types) {
            if parameter.ty == CodeType::Genvar && !mappings.contains_key(parameter) {
                let mut actual = ty.clone();
                if let Some(signature) = actual
                    .value
                    .as_deref()
                    .and_then(|name| self.cx.classes().get_class(name))
                    .and_then(|class| class.signature())
                    && actual != signature.generic_type
                {
                    actual = signature.generic_type.resize_array_dim(actual.array_dim);
                }
                mappings.insert(parameter.clone(), Some(actual));
            }
        }

        let key = &sam_signature.return_type;
        if key.ty == CodeType::Genvar {
            if method.name == INIT_NAME {
                let actual = method_class_signature.as_ref().map_or_else(
                    || {
                        VarType::with_value(
                            CodeType::Object,
                            0,
                            method_class.qualified_name.clone(),
                        )
                    },
                    |signature| signature.generic_type.clone(),
                );
                mappings.insert(key.clone(), Some(actual));
            } else if method_signature.is_some() || descriptor.ret != VarType::VARTYPE_OBJECT {
                let current = mappings.get(key).cloned().flatten();
                let mut actual = method_signature.as_ref().map_or_else(
                    || Some(descriptor.ret.clone()),
                    |sig| sig.return_type.remap_for_inference(&instance_map),
                );
                if !method_reference
                    && let Some(actual_type) = actual.as_ref()
                    && let Some(signature) = actual_type
                        .value
                        .as_deref()
                        .and_then(|name| self.cx.classes().get_class(name))
                        .and_then(|class| class.signature())
                    && !signature.generic_type.equals_exact(actual_type)
                {
                    let return_bound = current
                        .as_ref()
                        .filter(|ty| **ty == *actual_type)
                        .unwrap_or(actual_type);
                    if let Some(inferred) = self.lambda_return_type(
                        node_id,
                        &info,
                        &sam_signature,
                        return_bound,
                        &mappings,
                    )? {
                        actual = Some(inferred);
                    }
                }
                let named = self.named_generics();
                let replace = match (&current, &actual) {
                    (Some(current), Some(actual)) => {
                        actual.is_generic()
                            || (actual != current
                                && (current.ty != CodeType::Genvar || !named.contains_key(current)))
                    }
                    _ => true,
                };
                if replace {
                    let retain = if let Some(prior) = &current
                        && prior.is_generic()
                        && !prior.is_type_unfinished()
                    {
                        let actual = actual
                            .as_ref()
                            .ok_or_else(|| invalid("Null lambda return type"))?;
                        instance_of(self.cx, actual, prior)
                    } else {
                        false
                    };
                    if !retain {
                        mappings.insert(key.clone(), actual);
                    }
                }
            }
        }

        for var in ret.get_all_generic_vars() {
            if mappings.get(&var).is_none_or(Option::is_none) {
                mappings.insert(var, Some(GenericType::dummy_var()));
            }
        }
        if let Some(result) = ret.remap_for_inference(&mappings)
            && !result.same_generic_reference(ret)
        {
            if !result.is_generic()
                || !result.has_unknown_generic_type(&filtered_names(&self.named_generics()))
            {
                self.allocation_state(expr).inferred_lambda_type = Some(result.clone());
            }
            return Ok(Some(result));
        }
        Ok(None)
    }

    fn lambda_return_type(
        &mut self,
        node: ClassNodeId,
        info: &LambdaInformation,
        sam: &GenericMethodDescriptor,
        upper: &VarType,
        mappings: &GenericsMap,
    ) -> io::Result<Option<VarType>> {
        let Some(owner) = self.cx.class_nodes.wrapper_owner(node) else {
            return Ok(None);
        };
        let class = &self.cx.class_nodes[owner];
        let Some(wrapper) = &class.wrapper else {
            return Ok(None);
        };
        let Some(index) = class
            .class
            .methods
            .index_of_key(info.content_method_key.as_str())
        else {
            return Ok(None);
        };
        let method = &wrapper.methods[index];
        let Ok(Some(body)) = &method.body else {
            return Ok(None);
        };
        let processor = method.variables;
        let root = body.root;

        let body_descriptor = MethodDescriptor::parse_descriptor(&info.content_method_descriptor);
        let factory_descriptor = MethodDescriptor::parse_descriptor(&info.method_descriptor);
        let captured = body_descriptor
            .params
            .len()
            .saturating_sub(factory_descriptor.params.len());
        let mut temporary = Vec::new();
        for (index, (slot, _)) in body_descriptor
            .parameter_slots(info.is_content_method_static)
            .skip(captured)
            .enumerate()
        {
            let pair = VarVersionPair::new(slot, 0);
            let param = sam
                .parameter_types
                .get(index)
                .ok_or_else(|| invalid("Missing lambda SAM parameter"))?;
            if let Some(inferred) = param
                .remap_for_inference(mappings)
                .filter(|ty| *ty != VarType::VARTYPE_VOID)
            {
                let current = self.cx.ir[processor]
                    .versions
                    .lower
                    .get(&pair)
                    .ok_or_else(|| invalid("Missing lambda parameter type"))?;
                if *current != inferred
                    || (inferred.is_generic() && !inferred.equals_exact(current))
                {
                    let name = self.cx.ir[processor].names.get(&pair).cloned().flatten();
                    temporary.push(name.clone());
                    self.lambda_variables.insert(name, inferred);
                }
            }
        }

        let result = self.infer_lambda_return(root, upper);
        for name in temporary {
            self.lambda_variables.remove(&name);
        }
        result
    }

    fn infer_lambda_return(
        &mut self,
        root: crate::decompiler::ir::StatId,
        upper: &VarType,
    ) -> io::Result<Option<VarType>> {
        let StatementKind::Root { dummy_exit, .. } = self.cx.ir[root].kind else {
            unreachable!()
        };
        let incoming = self.cx.ir[dummy_exit].all_predecessors().to_vec();
        for edge in incoming {
            let source = self.cx.ir[edge].source;
            let Some(expr) = self.cx.ir[source]
                .exprents
                .and_then(|list| self.cx.ir[list].last().copied())
            else {
                continue;
            };
            if let ExprKind::Exit {
                kind: ExitType::Return,
                value,
                ..
            } = self.cx.ir[expr].kind
            {
                let value = value.ok_or_else(|| invalid("Missing lambda return expression"))?;
                let inferred = self.infer(value, Some(upper))?;
                if inferred.is_generic() {
                    return Ok(Some(inferred));
                }
            }
        }
        Ok(None)
    }
}
