// Copyright 2000-2018 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Eliminate synthetic accessors between classes in the same nested tree.

use std::io;

use arcstr::ArcStr;
use rustc_hash::FxHashMap;

use crate::code::code_constants::ACC_STATIC;
use crate::decompiler::exps::{ExitType, Expr, ExprKind, Variable};
use crate::decompiler::ir::{ExprId, Ir};
use crate::decompiler::vars::processor::VarNamesCollector;
use crate::engine::Cx;
use crate::engine::class_nodes::{ClassKind, ClassNodeId, ClassNodes};
use crate::engine::class_wrapper::MethodSlot;
use crate::engine::counter_container::{CounterContainer, VAR_COUNTER};
use crate::structs::StructMember;
use crate::types::{MethodDescriptor, VarType};
use crate::util::interpreter_util::make_unique_key;

#[derive(Clone, Copy)]
enum Access {
    FieldGet,
    FieldSet,
    Method,
    Increment,
}

struct Accessors<'a> {
    cx: &'a mut Cx,
    kinds: FxHashMap<(ClassNodeId, usize), Access>,
}

/// `NestedMemberAccess.propagateMemberAccess`, after all wrappers and captures
/// of the root class have been processed.
pub(crate) fn propagate_member_access(cx: &mut Cx, root: ClassNodeId) -> io::Result<()> {
    if cx.class_nodes[root].nested.is_empty() {
        return Ok(());
    }
    let mut pass = Accessors {
        cx,
        kinds: FxHashMap::default(),
    };
    pass.classify_classes(root)?;
    pass.rewrite_class(root)
}

impl Accessors<'_> {
    fn classify_classes(&mut self, node: ClassNodeId) -> io::Result<()> {
        if self.cx.class_nodes[node].kind == ClassKind::Lambda {
            return Ok(());
        }
        for child in self.cx.class_nodes[node].nested.clone() {
            self.classify_classes(child)?;
        }
        for index in 0..self.method_count(node)? {
            self.classify(MethodSlot { node, index });
        }
        Ok(())
    }

    fn method_count(&self, node: ClassNodeId) -> io::Result<usize> {
        self.cx.class_nodes[node]
            .wrapper
            .as_ref()
            .map(|wrapper| wrapper.methods.len())
            .ok_or_else(|| invalid("Class wrapper missing during synthetic accessor propagation"))
    }

    fn classify(&mut self, slot: MethodSlot) {
        let key = (slot.node, slot.index);
        if let Some(access) = self.classify_body(slot) {
            self.kinds.insert(key, access);
        } else {
            self.kinds.remove(&key);
        }
    }

    fn classify_body(&mut self, slot: MethodSlot) -> Option<Access> {
        let method = slot.get(self.cx);
        if !matches!(method.body, Ok(Some(_))) {
            return None;
        }
        let mt = method.method.clone();
        let graph = self.cx.wrapper_graph(slot);
        let (nodes, list) = (graph.order.len(), graph[graph.first].exprents);
        if nodes != 2
            || !mt.has_modifier(ACC_STATIC)
            || (!self.cx.options.synthetic_not_set && !mt.is_synthetic())
        {
            return None;
        }

        let class = &self.cx.class_nodes[slot.node].class.qualified_name;
        let descriptor = MethodDescriptor::parse_descriptor(&mt.descriptor);
        let count = descriptor.params.len();
        let ir = &self.cx.ir;
        match *ir[list].as_slice() {
            [expr] => {
                let core = returned_value(ir, expr).unwrap_or(expr);
                match &ir[core].kind {
                    ExprKind::Field(_) if field_accessor(ir, core, class, count, 0) => {
                        Some(Access::FieldGet)
                    }
                    ExprKind::Variable(var) if count == 1 && var.index != 0 => {
                        Some(Access::FieldGet)
                    }
                    ExprKind::Function { op, operands, .. }
                        if op.is_inc_dec()
                            && matches!(ir[operands[0]].kind, ExprKind::Field(_)) =>
                    {
                        Some(Access::Increment)
                    }
                    ExprKind::Invocation(call) => {
                        let start = usize::from(!call.is_static);
                        if call.parameters.len() + start != count
                            || (start != 0 && !variable_at(ir, call.instance, 0))
                        {
                            return None;
                        }
                        let parameters = descriptor.parameter_slots(true).skip(start);
                        call.parameters
                            .iter()
                            .zip(parameters)
                            .all(|(&param, (index, _))| variable_at(ir, Some(param), index))
                            .then_some(Access::Method)
                    }
                    ExprKind::Assignment { .. } if field_assignment(ir, core, class, count) => {
                        Some(Access::FieldSet)
                    }
                    _ => None,
                }
            }
            [assignment, exit]
                if field_assignment(ir, assignment, class, count)
                    && returned_value(ir, exit)
                        .is_some_and(|id| Expr::variable(ir, id).is_some()) =>
            {
                Some(Access::FieldSet)
            }
            _ => None,
        }
    }

    fn rewrite_class(&mut self, node: ClassNodeId) -> io::Result<()> {
        if self.cx.class_nodes[node].kind == ClassKind::Lambda {
            return Ok(());
        }

        for index in 0..self.method_count(node)? {
            let method = MethodSlot { node, index };
            if !matches!(method.get(self.cx).body, Ok(Some(_))) {
                continue;
            }
            let mut changed = false;
            for list in self.cx.wrapper_expr_lists(method) {
                for i in 0..self.cx.ir[list].len() {
                    let expr = self.cx.ir[list][i];
                    changed |= self.rewrite_children(method, expr)?;
                    if let Some(replacement) = self.replacement(method, expr)? {
                        self.cx.ir[list][i] = replacement;
                        changed = true;
                    }
                }
            }
            if changed {
                self.classify(method);
            }
        }

        for child in self.cx.class_nodes[node].nested.clone() {
            self.rewrite_class(child)?;
        }
        Ok(())
    }

    fn rewrite_children(&mut self, method: MethodSlot, parent: ExprId) -> io::Result<bool> {
        let children: Vec<_> = Expr::children(&self.cx.ir, parent).collect();
        let mut changed = false;
        for child in children {
            changed |= self.rewrite_children(method, child)?;
        }

        // A replacement can itself be another invocation. Iterate immediate
        // children again after each successful substitution.
        loop {
            let children: Vec<_> = Expr::children(&self.cx.ir, parent)
                .filter(|&expr| matches!(self.cx.ir[expr].kind, ExprKind::Invocation(_)))
                .collect();
            let mut replacement = None;
            for child in children {
                if let Some(new) = self.replacement(method, child)? {
                    replacement = Some((child, new));
                    break;
                }
            }
            let Some((old, new)) = replacement else {
                return Ok(changed);
            };
            Expr::replace(&mut self.cx.ir, parent, old, new);
            changed = true;
        }
    }

    fn replacement(&mut self, dest: MethodSlot, expr: ExprId) -> io::Result<Option<ExprId>> {
        let ExprKind::Invocation(call) = &self.cx.ir[expr].kind else {
            return Ok(None);
        };
        let Some(callee) = call
            .classname
            .as_deref()
            .and_then(|name| self.cx.class_nodes.id(name))
        else {
            return Ok(None);
        };
        let key = make_unique_key(&call.name, call.string_descriptor());
        let Some(source) = MethodSlot::by_key(self.cx, callee, &key) else {
            return Ok(None);
        };
        let Some(&access) = self.kinds.get(&(source.node, source.index)) else {
            return Ok(None);
        };
        if !same_tree(&self.cx.class_nodes, dest.node, callee) {
            return Ok(None);
        }

        let arguments = call.parameters.clone();
        let graph = self.cx.wrapper_graph(source);
        let first = graph[graph.first].exprents;
        let source_expr = *self.cx.ir[first]
            .first()
            .ok_or_else(|| invalid("Accessor lost its first expression"))?;
        let Some(replacement) = self.expand(access, dest, source, source_expr, &arguments)? else {
            return Ok(None);
        };
        self.cx.ir[replacement].bytecode = self.cx.ir[expr].bytecode.clone();

        let owner = &self.cx.class_nodes[callee];
        let require_synthetic = owner.kind == ClassKind::Root || owner.access & ACC_STATIC != 0;
        if !require_synthetic || source.get(self.cx).method.is_synthetic() {
            self.cx.class_nodes[source.node].hidden_members.insert(key);
        }
        Ok(Some(replacement))
    }

    fn expand(
        &mut self,
        access: Access,
        dest: MethodSlot,
        source: MethodSlot,
        expr: ExprId,
        arguments: &[ExprId],
    ) -> io::Result<Option<ExprId>> {
        let result = match access {
            Access::FieldGet => {
                let value = returned_value(&self.cx.ir, expr)
                    .ok_or_else(|| invalid("Getter accessor has no return value"))?;
                if let Some(var) = Expr::variable(&self.cx.ir, value) {
                    let owner = source.get(self.cx).variables;
                    let name = self.cx.ir[owner].names.get(&var.pair()).cloned().flatten();
                    let ty = Expr::expr_type(self.cx, value);
                    self.qualified_this(dest, name, ty)
                } else {
                    let field = copy_ambient(self.cx, value);
                    let instance = self.field_instance(field)?;
                    if let Some(instance) = instance {
                        Expr::replace(&mut self.cx.ir, field, instance, argument(arguments, 0)?);
                    }
                    field
                }
            }
            Access::FieldSet => {
                let assignment =
                    copy_ambient(self.cx, returned_value(&self.cx.ir, expr).unwrap_or(expr));
                let ExprKind::Assignment { left, right, .. } = self.cx.ir[assignment].kind else {
                    return Err(invalid("Setter accessor has no assignment"));
                };
                let receiver = self.field_instance(left)?;
                let value = argument(arguments, usize::from(receiver.is_some()))?;
                Expr::replace(&mut self.cx.ir, assignment, right, value);
                if let Some(instance) = receiver {
                    Expr::replace(&mut self.cx.ir, left, instance, argument(arguments, 0)?);
                }
                self.cx.ir[left].bytecode = None;
                self.cx.ir[value].bytecode = None;
                assignment
            }
            Access::Increment => {
                let value = returned_value(&self.cx.ir, expr)
                    .ok_or_else(|| invalid("Increment accessor has no return value"))?;
                // The upstream copy also consumes IDs if the arity check fails.
                let increment = copy_ambient(self.cx, value);
                let ExprKind::Function { operands, .. } = &self.cx.ir[increment].kind else {
                    return Err(invalid("Increment accessor has no operation"));
                };
                let field = operands[0];
                let receiver = self.field_instance(field)?;
                if arguments.len() != usize::from(receiver.is_some()) {
                    return Ok(None);
                }
                if let Some(instance) = receiver {
                    Expr::replace(&mut self.cx.ir, field, instance, arguments[0]);
                }
                increment
            }
            Access::Method => {
                let call = copy_ambient(self.cx, returned_value(&self.cx.ir, expr).unwrap_or(expr));
                let ExprKind::Invocation(invocation) = &self.cx.ir[call].kind else {
                    return Err(invalid("Method accessor has no invocation"));
                };
                let (is_static, receiver, count) = (
                    invocation.is_static,
                    invocation.instance,
                    invocation.parameters.len(),
                );
                let start = usize::from(!is_static);
                if !is_static {
                    let instance =
                        receiver.ok_or_else(|| invalid("Method accessor has no receiver"))?;
                    Expr::replace(&mut self.cx.ir, call, instance, argument(arguments, 0)?);
                }
                for index in 0..count {
                    let ExprKind::Invocation(invocation) = &self.cx.ir[call].kind else {
                        unreachable!()
                    };
                    let original = invocation.parameters[index];
                    Expr::replace(
                        &mut self.cx.ir,
                        call,
                        original,
                        argument(arguments, index + start)?,
                    );
                }
                call
            }
        };
        Ok(Some(result))
    }

    fn field_instance(&self, expr: ExprId) -> io::Result<Option<ExprId>> {
        let ExprKind::Field(field) = &self.cx.ir[expr].kind else {
            return Err(invalid("Synthetic accessor has no field"));
        };
        Ok(field.instance)
    }

    fn qualified_this(&mut self, dest: MethodSlot, name: Option<ArcStr>, ty: VarType) -> ExprId {
        let owner = dest.get(self.cx).variables;
        if dest.get_mut(self.cx).outer_var_names.insert(name.clone()) {
            let mut collector = VarNamesCollector::default();
            collector.used.insert(name.clone());
            self.cx.ir[owner].refresh_names(&mut collector);
        }
        let Ok(Some(body)) = &mut dest.get_mut(self.cx).body else {
            unreachable!()
        };
        let index = body.counters.get_counter_and_increment(VAR_COUNTER);
        let var = Variable::in_method(index, ty, owner);
        self.cx.ir[owner].names.insert(var.pair(), name);
        Expr::new_ambient(self.cx, ExprKind::Variable(var), None)
    }
}

fn field_accessor(ir: &Ir, expr: ExprId, class: &str, count: usize, values: usize) -> bool {
    let ExprKind::Field(field) = &ir[expr].kind else {
        return false;
    };
    field.classname.as_deref() == Some(class)
        && count == usize::from(!field.is_static()) + values
        && (field.is_static() || variable_at(ir, field.instance, 0))
}

fn field_assignment(ir: &Ir, expr: ExprId, class: &str, count: usize) -> bool {
    let ExprKind::Assignment { left, right, .. } = ir[expr].kind else {
        return false;
    };
    field_accessor(ir, left, class, count, 1) && variable_at(ir, Some(right), count as i32 - 1)
}

fn variable_at(ir: &Ir, expr: Option<ExprId>, index: i32) -> bool {
    expr.and_then(|id| Expr::variable(ir, id))
        .is_some_and(|var| var.index == index)
}

fn returned_value(ir: &Ir, expr: ExprId) -> Option<ExprId> {
    match ir[expr].kind {
        ExprKind::Exit {
            kind: ExitType::Return,
            value,
            ..
        } => value,
        _ => None,
    }
}

fn same_tree(classes: &ClassNodes, caller: ClassNodeId, callee: ClassNodeId) -> bool {
    // The qualified-name check also excludes recursive calls to the same method.
    if classes[caller].class.qualified_name == classes[callee].class.qualified_name {
        return false;
    }
    let root = |mut node: ClassNodeId| {
        while let Some(parent) = classes[node].parent {
            node = parent;
        }
        node
    };
    root(caller) == root(callee)
}

fn copy_ambient(cx: &mut Cx, expr: ExprId) -> ExprId {
    let mut counters = CounterContainer::with_expression_ids(cx.expression_ids.clone());
    Expr::copy(cx, &mut counters, expr)
}

fn argument(arguments: &[ExprId], index: usize) -> io::Result<ExprId> {
    arguments
        .get(index)
        .copied()
        .ok_or_else(|| invalid("Missing synthetic accessor argument"))
}

fn invalid(reason: &str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}
