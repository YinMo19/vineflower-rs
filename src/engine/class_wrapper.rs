// Copyright 2000-2024 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Method results published together at the end of ClassWrapper.init.

use arcstr::ArcStr;
use indexmap::IndexSet;
use rustc_hash::FxHashSet;
use std::any::Any;
use std::io;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::Arc;

use super::class_nodes::ClassNodeId;
use super::context::Cx;
use super::counter_container::CounterContainer;
use super::method_processor::ExpressionMethod;
use super::method_timeout::{self, MethodTimeout};
use crate::decompiler::flow::{DirectGraph, flatten::build_direct_graph};
use crate::decompiler::ir::{ExprId, ExprListId, Ir, IrNode, StatId, VarProcessorId};
use crate::decompiler::stats::StatementKind;
use crate::decompiler::vars::{processor::VarNamesCollector, var_version_pair::VarVersionPair};
use crate::structs::{StructClass, StructMethod};
use crate::util::interpreter_util::make_unique_key;
use crate::util::vb_style_collection::VBStyleCollection;

/// Methods follow the declaring class's method table, including native,
/// abstract and individually failed methods.
pub struct ClassWrapper {
    pub methods: Vec<MethodWrapper>,
    /// Encounter order of assignments. The writer follows the class field table.
    pub static_field_initializers: VBStyleCollection<ExprId, String>,
    pub dynamic_field_initializers: VBStyleCollection<ExprId, String>,
}

impl ClassWrapper {
    pub(crate) fn visit_ir_roots(&self, visit: &mut impl FnMut(IrNode)) {
        for method in &self.methods {
            method.visit_ir_roots(visit);
        }
        for &expr in self
            .static_field_initializers
            .iter()
            .chain(&self.dynamic_field_initializers)
        {
            visit(expr.into());
        }
    }
}

pub struct MethodWrapper {
    pub method: Arc<StructMethod>,
    pub body: io::Result<Option<MethodBody>>,
    pub variables: VarProcessorId,
    /// Available even for a failed, abstract or native method.
    pub counters: CounterContainer,
    pub synthetic_parameters: Option<Vec<Option<VarVersionPair>>>,
    pub outer_var_names: FxHashSet<Option<ArcStr>>,
    pub comment_lines: Option<IndexSet<String>>,
    pub add_error_comment: bool,
    pub is_compact_record_constructor: bool,
    /// A class-level processing failure leaves the method tree available.
    pub(super) write_error: Option<io::Error>,
}

impl MethodWrapper {
    pub(super) fn visit_ir_roots(&self, visit: &mut impl FnMut(IrNode)) {
        visit(self.variables.into());
        if let Ok(Some(body)) = &self.body {
            visit(body.root.into());
            if let Some(graph) = &body.graph {
                graph.visit_ir_roots(visit);
            }
        }
    }

    pub fn root(&self) -> Option<StatId> {
        self.body.as_ref().ok()?.as_ref().map(|body| body.root)
    }

    pub fn decompile_error(&self) -> Option<&io::Error> {
        self.write_error
            .as_ref()
            .or_else(|| self.body.as_ref().err())
    }

    pub(super) fn add_comment(&mut self, comment: &str) {
        self.comment_lines
            .get_or_insert_with(IndexSet::new)
            .insert(comment.to_owned());
    }
}

pub struct MethodBody {
    pub root: StatId,
    pub counters: CounterContainer,
    graph: Option<DirectGraph>,
}

impl MethodBody {
    pub fn graph(&mut self, ir: &mut Ir) -> &DirectGraph {
        self.graph
            .get_or_insert_with(|| build_direct_graph(ir, self.root))
    }
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
    order.into_iter().try_for_each(|node| {
        cx.with_class_node(node, |cx| {
            let class = Arc::clone(&cx.class_nodes[node].class);
            cx.current_class = Some(Arc::clone(&class));
            class.prepare_method_properties();
            // Each declared method gets a slot, including methods without Code.
            let mut methods = Vec::with_capacity(class.methods.len());
            for method in &class.methods {
                methods.push(process_method(cx, &class, method, &mut process)?);
            }
            cx.class_nodes[node].wrapper = Some(ClassWrapper {
                methods,
                static_field_initializers: VBStyleCollection::new(),
                dynamic_field_initializers: VBStyleCollection::new(),
            });
            Ok(())
        })
    })
}

pub(crate) fn catch_method_failure<T>(process: impl FnOnce() -> io::Result<T>) -> io::Result<T> {
    catch_unwind(AssertUnwindSafe(process)).map_err(method_error_from_panic)?
}

pub(super) fn method_error_from_panic(payload: Box<dyn Any + Send>) -> io::Error {
    if payload.is::<MethodTimeout>() {
        return io::Error::new(io::ErrorKind::TimedOut, MethodTimeout);
    }
    let reason = payload
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| payload.downcast_ref::<&str>().copied())
        .unwrap_or("Unrecognized method processing failure");
    io::Error::other(reason.to_owned())
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
    // startMethod installs a new sequence even for methods without code. The
    // last method remains the ambient sequence during nested-class processing.
    let (variables, expression_ids) = cx
        .prepared_methods
        .as_mut()
        .and_then(|prepared| prepared.start_method(method, &cx.class_nodes))
        .unwrap_or_else(|| {
            (
                cx.ir.variable_processors.push(Default::default()),
                Default::default(),
            )
        });
    cx.expression_ids = expression_ids;
    let previous = cx.current_method.replace((Arc::clone(method), variables));
    let outcome = catch_method_failure(|| {
        if let Some(seconds) = cx.options.method_time_limit()
            && method.contains_code()
        {
            method_timeout::run(seconds, || process(cx, class, method))
        } else {
            process(cx, class, method)
        }
    });
    cx.current_method = previous;
    let variables = outcome
        .as_ref()
        .ok()
        .and_then(Option::as_ref)
        .map_or(variables, |method| method.flow.variables);
    let (comment_lines, add_error_comment) = if let Ok(Some(body)) = &outcome
        && let StatementKind::Root {
            comment_lines: Some(comments),
            add_error_comment,
            ..
        } = &cx.ir[body.root].kind
    {
        (
            (!comments.is_empty()).then(|| comments.clone()),
            *add_error_comment,
        )
    } else {
        (None, false)
    };
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
            if cx.options.use_lvt_names
                && processor.definitions_set
                && let Some(method_body) = &result
            {
                crate::decompiler::vars::processor::apply_debug_names(
                    cx,
                    method_body.root,
                    variables,
                    method,
                )?;
            }
            Ok(result.map(MethodBody::from))
        }
        Err(error) if error.kind() == io::ErrorKind::Interrupted => return Err(error),
        Err(error) if error.get_ref().is_some_and(|cause| cause.is::<MethodTimeout>()) => {
            log::error!(
                "Processing time limit exceeded for method {}, execution interrupted.",
                method.name
            );
            Err(error)
        }
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
    let counters = body.as_ref().ok().and_then(Option::as_ref).map_or_else(
        || CounterContainer::with_expression_ids(cx.expression_ids.clone()),
        |body| body.counters.shared(),
    );
    Ok(MethodWrapper {
        method: Arc::clone(method),
        variables,
        counters,
        synthetic_parameters: None,
        outer_var_names: Default::default(),
        comment_lines,
        add_error_comment,
        write_error: None,
        is_compact_record_constructor: false,
        body,
    })
}

#[derive(Clone, Copy)]
pub(crate) struct MethodSlot {
    pub(super) node: ClassNodeId,
    pub(super) index: usize,
}

impl MethodSlot {
    pub(crate) fn at(node: ClassNodeId, index: usize) -> Self {
        Self { node, index }
    }

    pub(crate) fn by_key(cx: &Cx, node: ClassNodeId, key: &str) -> Option<Self> {
        let node = cx.class_nodes.wrapper_owner(node)?;
        let class = &cx.class_nodes[node];
        class.wrapper.as_ref()?;
        let index = class.class.methods.index_of_key(key)?;
        Some(Self { node, index })
    }

    /// Temporarily select a method without changing the writing class.
    pub(crate) fn with_current<T>(self, cx: &mut Cx, write: impl FnOnce(&mut Cx) -> T) -> T {
        struct Scope<'a> {
            cx: &'a mut Cx,
            previous: Option<MethodSlot>,
        }

        impl Drop for Scope<'_> {
            fn drop(&mut self) {
                self.cx.current_method_wrapper = self.previous;
            }
        }

        let previous = cx.current_method_wrapper.replace(self);
        write(Scope { cx, previous }.cx)
    }

    pub(crate) fn get(self, cx: &Cx) -> &MethodWrapper {
        &cx.class_nodes[self.node].wrapper.as_ref().unwrap().methods[self.index]
    }

    pub(crate) fn record_write_error(self, cx: &mut Cx, error: io::Error) {
        self.get_mut(cx).write_error = Some(error);
    }

    pub(crate) fn index(self) -> usize {
        self.index
    }

    pub(super) fn get_mut(self, cx: &mut Cx) -> &mut MethodWrapper {
        &mut cx.class_nodes[self.node].wrapper.as_mut().unwrap().methods[self.index]
    }
}

pub(crate) enum WrapperMethod {
    NoClassNode,
    Unpublished,
    Missing,
    NoRoot,
    Ready { root: StatId, method: MethodSlot },
}

impl Cx {
    /// Class writing selects a published wrapper. Method analysis has only its
    /// StructMethod and VarProcessor until publication is complete.
    pub(crate) fn writing_method(&self) -> Option<&MethodWrapper> {
        let slot = self.current_method_wrapper?;
        self.class_nodes[slot.node]
            .wrapper
            .as_ref()?
            .methods
            .get(slot.index)
    }

    pub(crate) fn method_wrapper_by_key(
        &self,
        node: ClassNodeId,
        key: &str,
    ) -> Option<&MethodWrapper> {
        MethodSlot::by_key(self, node, key).map(|slot| slot.get(self))
    }

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
        let graph = self.wrapper_graph(method);
        graph
            .regular_breadth_first()
            .map(|node| graph[node].exprents)
            .collect()
    }

    pub(crate) fn wrapper_graph(&mut self, method: MethodSlot) -> &DirectGraph {
        let wrapper = self.class_nodes[method.node]
            .wrapper
            .as_mut()
            .expect("Unpublished class wrapper");
        let Ok(Some(body)) = &mut wrapper.methods[method.index].body else {
            unreachable!()
        };
        body.graph(&mut self.ir)
    }
}
