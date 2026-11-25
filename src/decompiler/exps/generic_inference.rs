// Copyright 2000-2024 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! The state and expression dispatch of Exprent.getInferredExprType.

mod allocation;
mod bounds;
mod invocation;

use std::{fmt, io, sync::Arc};

use arcstr::ArcStr;
use rustc_hash::FxHashSet;

use super::{Expr, ExprKind, Field, FunctionType, Invocation};
use crate::decompiler::ir::ExprId;
use crate::engine::Cx;
use crate::structs::{StructClass, StructMethod};
use crate::types::{CodeType, GenericType, GenericsMap, NamedGenerics, VarType};
use crate::util::jhash::{JHashMap, JHashSet};

#[derive(Clone, Default)]
pub struct InvocationGenerics {
    pub resolved_method: Option<Arc<StructMethod>>,
    pub arguments: Vec<VarType>,
    pub mappings: GenericsMap,
    pub remapped_instance: Option<VarType>,
    pub is_invocation_instance: bool,
    pub force_qualification: bool,
    pub keep_unboxing_cast: bool,
}

impl fmt::Debug for InvocationGenerics {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let method = self
            .resolved_method
            .as_deref()
            .map(|m| (&m.class_qualified_name, &m.name, &m.descriptor));
        f.debug_struct("InvocationGenerics")
            .field("resolved_method", &method)
            .field("arguments", &self.arguments)
            .field("mappings", &self.mappings.iter().collect::<Vec<_>>())
            .field("remapped_instance", &self.remapped_instance)
            .field("is_invocation_instance", &self.is_invocation_instance)
            .field("force_qualification", &self.force_qualification)
            .field("keep_unboxing_cast", &self.keep_unboxing_cast)
            .finish()
    }
}

#[derive(Clone, Debug, Default)]
pub struct AllocationGenerics {
    pub arguments: Vec<VarType>,
    pub inferred_lambda_type: Option<VarType>,
}

impl Invocation {
    pub(crate) fn resolve_description(cx: &mut Cx, expr: ExprId) -> Option<Arc<StructMethod>> {
        let call = invocation(&cx.ir, expr);
        if let Some(method) = call
            .generics
            .as_ref()
            .and_then(|g| g.resolved_method.as_ref())
        {
            return Some(Arc::clone(method));
        }
        let owner = cx.classes().get_class(call.classname.as_deref()?)?;
        let method = owner.get_method_recursive(cx, &call.name, call.string_descriptor())?;
        let ExprKind::Invocation(call) = &mut cx.ir[expr].kind else {
            unreachable!()
        };
        call.generics
            .get_or_insert_with(Default::default)
            .resolved_method = Some(Arc::clone(&method));
        Some(method)
    }
}

pub(crate) struct Inference<'a> {
    pub cx: &'a mut Cx,
    active_method: Arc<StructMethod>,
    lambda_variables: JHashMap<Option<ArcStr>, VarType>,
    active: FxHashSet<ExprId>,
}

impl<'a> Inference<'a> {
    pub(crate) fn at_end(cx: &'a mut Cx, active_method: Arc<StructMethod>) -> Self {
        Self {
            cx,
            active_method,
            lambda_variables: JHashMap::new(),
            active: FxHashSet::default(),
        }
    }

    pub(crate) fn infer(
        &mut self,
        expr: ExprId,
        upper_bound: Option<&VarType>,
    ) -> io::Result<VarType> {
        if !self.active.insert(expr) {
            return Err(invalid("Recursive expression type inference"));
        }
        let result = self.infer_expression(expr, upper_bound);
        self.active.remove(&expr);
        result
    }

    fn infer_expression(
        &mut self,
        expr: ExprId,
        upper_bound: Option<&VarType>,
    ) -> io::Result<VarType> {
        let inferred = match &self.cx.ir[expr].kind {
            ExprKind::Invocation(_) => return self.infer_invocation(expr, upper_bound),
            ExprKind::New { .. } => return self.infer_allocation(expr, upper_bound),
            ExprKind::Variable(variable) => {
                if variable.lvt.is_none()
                    && variable
                        .var_type
                        .as_ref()
                        .is_none_or(|ty| ty.ty == CodeType::Unknown)
                    && let Some(processor) = variable.processor
                    && let Some(ty) = self.lambda_variables.get(
                        &self.cx.ir[processor]
                            .names
                            .get(&variable.pair())
                            .cloned()
                            .flatten(),
                    )
                {
                    ty.clone()
                } else {
                    variable.inferred_expr_type(self.cx)
                }
            }
            ExprKind::Assignment { left, .. } => return self.infer(*left, upper_bound),
            ExprKind::Array {
                array, hard_type, ..
            } => {
                let hard_type = hard_type.clone();
                let array = self.infer(*array, upper_bound)?;
                if array == VarType::VARTYPE_NULL {
                    hard_type
                } else {
                    array.decrease_array_dim()
                }
            }
            ExprKind::Field(field) => return self.infer_field(&field.as_ref().clone()),
            ExprKind::Function { op, operands, .. } => {
                return self.infer_function(expr, *op, operands.clone(), upper_bound);
            }
            _ => Expr::expr_type(self.cx, expr),
        };
        Ok(inferred)
    }

    pub(crate) fn invocation_state(&mut self, expr: ExprId) -> &mut InvocationGenerics {
        let ExprKind::Invocation(call) = &mut self.cx.ir[expr].kind else {
            unreachable!("Generic invocation state needs an invocation");
        };
        call.generics.get_or_insert_with(Default::default)
    }

    fn current_class(&self) -> Option<Arc<StructClass>> {
        self.cx
            .current_class_node
            .as_deref()
            .and_then(|name| self.cx.class_nodes.get(name))
            .map(|node| Arc::clone(&node.class))
    }

    fn named_generics(&self) -> NamedGenerics {
        let mut names = NamedGenerics::new();
        let mut class = self
            .cx
            .current_class_node
            .as_deref()
            .and_then(|name| self.cx.class_nodes.id(name));
        // There is no CURRENT_METHOD_WRAPPER during ClassWrapper.init.
        let mut method = None;
        loop {
            if let Some(signature) = class.and_then(|id| self.cx.class_nodes[id].class.signature())
            {
                assign_bounds(
                    &mut names,
                    &signature.fparameters,
                    &signature.fbounds,
                    false,
                );
            }
            if let Some(signature) = method.and_then(StructMethod::signature) {
                assign_bounds(
                    &mut names,
                    &signature.type_parameters,
                    &signature.type_parameter_bounds,
                    false,
                );
            }
            let Some(id) = class else { break };
            let node = &self.cx.class_nodes[id];
            let Some(parent) = node.parent else { break };
            let Some(owner) = self.cx.class_nodes.wrapper_owner(parent) else {
                break;
            };
            let parent_class = &self.cx.class_nodes[owner];
            if parent_class.wrapper.is_none() {
                break;
            }
            method = node
                .enclosing_method
                .as_deref()
                .and_then(|key| parent_class.class.get_method_by_key(key))
                .map(Arc::as_ref);
            class = Some(parent);
        }
        names
    }

    fn mark_instance(&mut self, expr: ExprId) {
        match &self.cx.ir[expr].kind {
            ExprKind::Invocation(_) => self.invocation_state(expr).is_invocation_instance = true,
            ExprKind::Function {
                op: FunctionType::Cast,
                operands,
                ..
            } => {
                self.mark_instance(operands[0]);
            }
            ExprKind::New {
                constructor: Some(constructor),
                ..
            } => self.mark_instance(*constructor),
            _ => {}
        }
    }

    fn skip_cast(&self, expr: ExprId) -> ExprId {
        match &self.cx.ir[expr].kind {
            ExprKind::Function {
                op: FunctionType::Cast,
                operands,
                ..
            } => operands[0],
            _ => expr,
        }
    }

    fn infer_field(&mut self, field: &Field) -> io::Result<VarType> {
        let erased = &field.descriptor.ty;
        let Some(owner) = field
            .classname
            .as_deref()
            .and_then(|n| self.cx.classes().get_class(n))
        else {
            return Ok(erased.clone());
        };
        let hierarchy = owner.get_all_generics(self.cx);
        let mut class = owner;
        loop {
            if let Some(ft) = class.get_field(&field.name, &field.descriptor.descriptor_string) {
                let Some(signature) = ft.shared_signature() else {
                    break;
                };
                let signature = signature.update(|s| {
                    s.verify_type(self.cx, class.signature().as_deref(), erased);
                    s.ty.clone()
                });
                let mut ty = match hierarchy.get(&class.qualified_name) {
                    Some(map) => signature
                        .remap_for_inference(map)
                        .ok_or_else(|| invalid("Null inferred field type"))?,
                    None => signature,
                };
                if let Some(instance) = field.instance
                    && class.signature().is_some()
                {
                    let receiver = self.infer(instance, None)?;
                    if receiver.is_generic()
                        && receiver.ty != CodeType::Genvar
                        && let Some(declared) = receiver
                            .value
                            .as_deref()
                            .and_then(|n| self.cx.classes().get_class(n))
                        && let Some(signature) = declared.signature()
                    {
                        let mut temporary = GenericsMap::new();
                        signature
                            .generic_type
                            .map_gen_vars_to(self.cx, &receiver, &mut temporary);
                        ty = ty
                            .remap_for_inference(&temporary)
                            .unwrap_or_else(|| erased.clone());
                    }
                }
                return Ok(ty);
            }
            let Some(parent) = class
                .super_class
                .as_ref()
                .and_then(|name| self.cx.classes().get_class(name.get_string()))
            else {
                break;
            };
            class = parent;
        }
        Ok(erased.clone())
    }

    fn infer_function(
        &mut self,
        expr: ExprId,
        op: FunctionType,
        operands: Vec<ExprId>,
        upper_bound: Option<&VarType>,
    ) -> io::Result<VarType> {
        match op {
            FunctionType::Cast => {
                let mut right = self.infer(operands[0], upper_bound)?;
                let cast: Vec<_> = operands[1..]
                    .iter()
                    .map(|&id| Expr::expr_type(self.cx, id))
                    .collect();
                let keep_cast;
                if let Some(mut upper) = upper_bound
                    .cloned()
                    .filter(|t| t.is_generic() || right.is_generic())
                {
                    let array_dim = if upper.array_dim == right.array_dim {
                        upper.array_dim
                    } else {
                        0
                    };
                    if array_dim > 0 {
                        upper = upper.resize_array_dim(0);
                        right = right.resize_array_dim(0);
                    }
                    let names = self.named_generics();
                    keep_cast = if let Some(types) = names.get(&right).or_else(|| names.get(&upper))
                    {
                        !cast
                            .iter()
                            .all(|cast| types.iter().any(|ty| instance_of(self.cx, ty, cast)))
                    } else {
                        right.ty == CodeType::Null
                            || !instance_of(self.cx, &right, &upper)
                            || !are_generic_cast_types_compatible(&right, &upper)
                    };
                    if !keep_cast && array_dim > 0 {
                        right = right.resize_array_dim(array_dim);
                    }
                } else {
                    keep_cast = right.ty == CodeType::Null
                        || cast.iter().any(|ty| !instance_of(self.cx, &right, ty))
                        || cast.iter().any(|ty| right.array_dim != ty.array_dim);
                }
                let ExprKind::Function { needs_cast, .. } = &mut self.cx.ir[expr].kind else {
                    unreachable!()
                };
                *needs_cast = keep_cast;
                if !keep_cast
                    && upper_bound.is_some_and(|upper| upper.is_generic() || right.is_generic())
                {
                    return Ok(right);
                }
            }
            FunctionType::Ternary => {
                let a = self.infer(operands[1], upper_bound)?;
                let b = self.infer(operands[2], upper_bound)?;
                if a.ty == CodeType::Null {
                    return Ok(b);
                }
                if b.ty == CodeType::Null {
                    return Ok(a);
                }
                if let Some(union) = VarType::join(self.cx, &a, &b) {
                    if union.ty != CodeType::Boolean
                        && matches!(self.cx.ir[operands[1]].kind, ExprKind::Constant { .. })
                        && matches!(self.cx.ir[operands[2]].kind, ExprKind::Constant { .. })
                        && VarType::VARTYPE_INT.higher_equal_in_lattice_than(self.cx, &union)
                    {
                        return Ok(VarType::VARTYPE_INT);
                    }
                    return Ok(union);
                }
            }
            _ => {
                let bound = if op == FunctionType::InstanceOf {
                    None
                } else {
                    upper_bound
                };
                for operand in operands {
                    self.infer(operand, bound)?;
                }
            }
        }
        Ok(Expr::expr_type(self.cx, expr))
    }
}

fn are_generic_cast_types_compatible(right: &VarType, upper: &VarType) -> bool {
    !right.is_generic_type()
        || !upper.is_generic_type()
        || (right.arguments().len() == upper.arguments().len()
            && right
                .arguments()
                .iter()
                .zip(upper.arguments())
                .all(|(right, upper)| upper.is_none() || right.is_some()))
}

fn instance_of(cx: &Cx, candidate: &VarType, bound: &VarType) -> bool {
    match (candidate.value.as_deref(), bound.value.as_deref()) {
        (Some(candidate), Some(bound)) => cx.classes().instance_of(candidate, bound),
        _ => false,
    }
}

fn name_type(name: &str) -> VarType {
    VarType::parse(&format!("T{name};"))
}

fn filtered_names(names: &NamedGenerics) -> JHashSet<VarType> {
    let mut keys = JHashSet::new();
    keys.extend(names.keys().cloned());
    keys
}

fn assign_bounds(
    names: &mut NamedGenerics,
    formals: &[String],
    bounds: &[Vec<VarType>],
    inherited: bool,
) {
    for (formal, bound) in formals.iter().zip(bounds) {
        let formal = name_type(formal);
        if !inherited || !names.contains_key(&formal) {
            names.insert(formal, bound.clone());
        }
    }
}

fn gather_generics(cx: &Cx, upper: Option<&VarType>, target: &VarType, map: &mut GenericsMap) {
    if let Some(upper) = upper
        && upper.is_generic()
        && target.is_generic()
        && upper.array_dim == target.array_dim
        && upper.arguments().len() == target.arguments().len()
    {
        target.map_gen_vars_to(cx, upper, map);
    }
}

fn generic_arguments(formals: &[String], mapping: &GenericsMap) -> Vec<VarType> {
    formals
        .iter()
        .map(|name| {
            mapping
                .get(&name_type(name))
                .and_then(Option::as_ref)
                .filter(|arg| arg.wildcard() == GenericType::WILDCARD_NO)
                .cloned()
        })
        .collect::<Option<_>>()
        .unwrap_or_default()
}

fn invalid(reason: &str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

fn invocation(ir: &crate::decompiler::ir::Ir, expr: ExprId) -> &Invocation {
    let ExprKind::Invocation(call) = &ir[expr].kind else {
        unreachable!("Expected invocation")
    };
    call
}
