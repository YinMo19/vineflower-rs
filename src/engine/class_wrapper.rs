// Copyright 2000-2024 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Method results published together at the end of ClassWrapper.init.

use std::io;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::Arc;

use super::class_nodes::ClassNodeId;
use super::context::Cx;
use super::counter_container::CounterContainer;
use super::method_processor::ExpressionMethod;
use crate::decompiler::flow::{DirectGraph, flatten::build_direct_graph};
use crate::decompiler::ir::{ExprListId, StatId, VarProcessorId};
use crate::decompiler::vars::processor::VarNamesCollector;
use crate::structs::{StructClass, StructMethod};
use crate::util::interpreter_util::make_unique_key;

/// Methods follow the declaring class's method table, including native,
/// abstract and individually failed methods.
pub struct ClassWrapper {
    pub methods: Vec<MethodWrapper>,
}

pub struct MethodWrapper {
    pub method: Arc<StructMethod>,
    pub body: io::Result<Option<MethodBody>>,
    pub variables: VarProcessorId,
}

pub struct MethodBody {
    pub root: StatId,
    pub counters: CounterContainer,
    graph: Option<DirectGraph>,
}

impl From<ExpressionMethod> for MethodBody {
    fn from(method: ExpressionMethod) -> Self {
        Self {
            root: method.root,
            counters: method.flow.counters,
            graph: None,
        }
    }
}

/// Publish each class only after its last method. The current class remains
/// private while its methods may already consult a completed sibling.
pub(super) fn initialize_wrappers(
    cx: &mut Cx,
    root: ClassNodeId,
    mut process: impl FnMut(
        &mut Cx,
        &StructClass,
        &Arc<StructMethod>,
    ) -> io::Result<Option<ExpressionMethod>>,
) -> io::Result<()> {
    let order = cx.class_nodes.wrapper_order(root).to_vec();
    let previous = cx.current_class_node.take();
    let result = order.into_iter().try_for_each(|node| {
        let class = Arc::clone(&cx.class_nodes[node].class);
        class.prepare_method_properties();
        cx.current_class_node = Some(class.qualified_name.clone());
        let methods = class
            .methods
            .iter()
            .map(|method| process_method(cx, &class, method, &mut process))
            .collect::<io::Result<_>>()?;
        cx.class_nodes[node].wrapper = Some(ClassWrapper { methods });
        Ok(())
    });
    cx.current_class_node = previous;
    result
}

fn process_method(
    cx: &mut Cx,
    class: &StructClass,
    method: &Arc<StructMethod>,
    process: &mut impl FnMut(
        &mut Cx,
        &StructClass,
        &Arc<StructMethod>,
    ) -> io::Result<Option<ExpressionMethod>>,
) -> io::Result<MethodWrapper> {
    // ClassWrapper catches failures at the method boundary. A failure in
    // graph recognition leaves other methods in this class available.
    let variables = cx.ir.variable_processors.push(Default::default());
    let previous = cx.current_method.replace((Arc::clone(method), variables));
    let outcome =
        catch_unwind(AssertUnwindSafe(|| process(cx, class, method))).unwrap_or_else(|payload| {
            let reason = payload
                .downcast_ref::<String>()
                .map(String::as_str)
                .or_else(|| payload.downcast_ref::<&str>().copied())
                .unwrap_or("Unrecognized method processing failure");
            Err(io::Error::other(reason.to_owned()))
        });
    cx.current_method = previous;
    let variables = outcome
        .as_ref()
        .ok()
        .and_then(Option::as_ref)
        .map_or(variables, |method| method.flow.variables);
    let body = match outcome {
        Ok(result) => {
            let processor = &mut cx.ir[variables];
            if result.is_none() && !method.contains_code() {
                processor.name_declared_parameters(class, method);
            }
            let mut collector = VarNamesCollector::default();
            for field in &class.fields {
                collector.add_name(&field.name);
            }
            processor.refresh_names(&mut collector);
            Ok(result.map(MethodBody::from))
        }
        Err(error) if error.kind() == io::ErrorKind::Interrupted => return Err(error),
        Err(error) => {
            log::warn!(
                "Could not decompile {}.{} {}: {error}",
                class.qualified_name,
                method.name,
                method.descriptor
            );
            Err(error)
        }
    };
    Ok(MethodWrapper {
        method: Arc::clone(method),
        variables,
        body,
    })
}

#[derive(Clone, Copy)]
pub(crate) struct MethodSlot {
    node: ClassNodeId,
    index: usize,
}

pub(crate) enum WrapperMethod {
    NoClassNode,
    Unpublished,
    Missing,
    NoRoot,
    Ready { root: StatId, method: MethodSlot },
}

impl Cx {
    pub(crate) fn wrapper_method(
        &self,
        owner: &str,
        name: &str,
        descriptor: &str,
    ) -> WrapperMethod {
        let Some(node) = self.class_nodes.id(owner) else {
            return WrapperMethod::NoClassNode;
        };
        let Some(node) = self.class_nodes.wrapper_owner(node) else {
            return WrapperMethod::Unpublished;
        };
        let class = &self.class_nodes[node];
        let Some(wrapper) = &class.wrapper else {
            return WrapperMethod::Unpublished;
        };
        let key = make_unique_key(name, descriptor);
        let Some(index) = class.class.methods.index_of_key(key.as_str()) else {
            return WrapperMethod::Missing;
        };
        match &wrapper.methods[index].body {
            Ok(Some(body)) => WrapperMethod::Ready {
                root: body.root,
                method: MethodSlot { node, index },
            },
            _ => WrapperMethod::NoRoot,
        }
    }

    /// Cache the direct graph, but read each node's live expression list in
    /// regular breadth-first order just as DirectGraph.iterateExprents does.
    pub(crate) fn wrapper_expr_lists(&mut self, method: MethodSlot) -> Vec<ExprListId> {
        let wrapper = self.class_nodes[method.node]
            .wrapper
            .as_mut()
            .expect("Unpublished class wrapper");
        let Ok(Some(body)) = &mut wrapper.methods[method.index].body else {
            unreachable!()
        };
        let graph = body
            .graph
            .get_or_insert_with(|| build_direct_graph(&mut self.ir, body.root));
        graph
            .regular_breadth_first()
            .map(|node| graph[node].exprents)
            .collect()
    }
}
