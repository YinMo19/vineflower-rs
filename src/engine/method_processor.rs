// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Method stages of `MethodProcessor.codeToJava` through expression lifting.
//!
//! The language-independent stages end immediately before upstream dispatches
//! to a language's CFG passes. Java then prepares exception regions for
//! `DomHelper`. The original graph remains available for finally processing.

use std::io;
use std::sync::Arc;

use indexmap::IndexSet;

use crate::code::{
    cfg::ControlFlowGraph, dead_code_helper as dead, exception_deobfuscator as exceptions,
};
use crate::decompiler::decompose::{
    dom_helper::{graph_to_statement, process_statement},
    finish::{condense_sequences, finish, prepare_expressions},
};
use crate::decompiler::{
    expr_processor,
    finally::FinallyProcessor,
    ir::{Ir, StatId},
};
use crate::engine::{
    Cx, Options,
    counter_container::{CounterContainer, VAR_COUNTER},
};
use crate::structs::{StructClass, StructMethod};
use crate::types::MethodDescriptor;

/// Per-method state. Graph handles belong to the enclosing root class's IR.
/// The counters follow the method when another method becomes current.
pub struct MethodGraph {
    pub graph: ControlFlowGraph,
    pub counters: CounterContainer,
}

/// A raw CFG retains the class and method whose constant pool and local types it uses.
pub struct DecodedMethod<'a> {
    pub flow: MethodGraph,
    class: &'a StructClass,
    method: &'a StructMethod,
}

/// The language-dispatch point after shared CFG cleanup.
pub struct CommonMethod<'a> {
    pub flow: MethodGraph,
    class: &'a StructClass,
}

impl<'a> DecodedMethod<'a> {
    /// Decodes a method's Code attribute. Abstract, native and library
    /// methods without retained code do not enter the graph pipeline.
    pub fn from_method(
        ir: &mut Ir,
        class: &'a StructClass,
        method: &'a StructMethod,
    ) -> io::Result<Option<Self>> {
        Ok(method.expand_data(class)?.map(|seq| {
            let graph = ControlFlowGraph::new(ir, seq);
            let mut counters = CounterContainer::default();
            counters.set_counter(VAR_COUNTER, method.local_variables);
            Self {
                flow: MethodGraph { graph, counters },
                class,
                method,
            }
        }))
    }

    pub fn prepare_control_flow(mut self, ir: &mut Ir, options: &Options) -> CommonMethod<'a> {
        let graph = &mut self.flow.graph;
        dead::remove_dead_blocks(ir, graph);
        if self.method.bytecode_version.has_jsr() || options.force_jsr_inline {
            graph.inline_jsr(ir, self.class, self.method, options);
        }
        dead::connect_dummy_exit_block(ir, graph);
        dead::remove_gotos(ir, graph, options);
        CommonMethod {
            flow: self.flow,
            class: self.class,
        }
    }
}

impl CommonMethod<'_> {
    pub fn prepare_java_graph(mut self, ir: &mut Ir, options: &Options) -> MethodGraph {
        let graph = &mut self.flow.graph;
        exceptions::remove_circular_ranges(ir, graph);
        exceptions::restore_pop_ranges(ir, graph);
        if options.remove_empty_try_catch {
            exceptions::remove_empty_ranges(ir, graph);
        }
        if options.ensure_synchronized_monitors {
            dead::extend_synchronized_range_to_monitorexit(ir, graph);
        }
        if options.incorporate_returns {
            dead::incorporate_value_returns(ir, graph);
        }
        exceptions::insert_empty_exception_handler_blocks(ir, graph);
        dead::merge_basic_blocks(ir, graph, options);
        if exceptions::has_obfuscated_exceptions(ir, graph) {
            if !exceptions::handle_multiple_entry_exception_ranges(ir, graph) {
                log::warn!("Found multiple entry exception ranges which could not be splitted");
                graph.add_comment("$VF: Could not handle exception ranges with multiple entries");
                graph.add_error_comment = true;
            }
            exceptions::insert_dummy_exception_handler_blocks(ir, graph, self.class, options);
        }
        self.flow
    }
}

/// The first statement graph for a Java method, together with the CFG from
/// which finally processing can build further revisions.
pub struct InitialMethod {
    pub flow: MethodGraph,
    pub root: StatId,
}

pub fn initial_statement_graph(
    cx: &mut Cx,
    class: &StructClass,
    method: &Arc<StructMethod>,
) -> io::Result<Option<InitialMethod>> {
    let Some(decoded) = DecodedMethod::from_method(&mut cx.ir, class, method)? else {
        return Ok(None);
    };
    let common = decoded.prepare_control_flow(&mut cx.ir, &cx.options);
    let mut flow = common.prepare_java_graph(&mut cx.ir, &cx.options);
    let root = flow.statement_root(&mut cx.ir, Arc::clone(method));
    Ok(Some(InitialMethod { flow, root }))
}

impl MethodGraph {
    fn statement_root(&mut self, ir: &mut Ir, method: Arc<StructMethod>) -> StatId {
        let root = graph_to_statement(ir, &mut self.counters, &self.graph, method);
        ir[root].add_graph_comments(&self.graph);
        root
    }
}

/// A Java method after the structure recognition and cleanup in DomHelper.parseGraph.
/// The CFG is retained because finally recovery can change it and require a new tree.
pub struct StructuredMethod {
    pub flow: MethodGraph,
    pub root: StatId,
    descriptor: Arc<MethodDescriptor>,
}

impl StructuredMethod {
    /// Rebuilds the tree from the rewritten CFG. Counters continue across parses.
    pub fn reparse(&mut self, cx: &mut Cx) -> io::Result<()> {
        let method = Arc::clone(self.root.method(&cx.ir));
        let root = self.flow.statement_root(&mut cx.ir, method);
        structure_root(cx, &mut self.flow.counters, root)?;
        root.add_comments_from(&mut cx.ir, self.root);
        self.root = root;
        Ok(())
    }

    pub fn recover_finally(
        mut self,
        cx: &mut Cx,
        class: &StructClass,
    ) -> io::Result<RecoveredMethod> {
        let mut processor = FinallyProcessor::default();
        while processor.iterate_graph(cx, class, &mut self)? {
            self.reparse(cx)?;
        }
        Ok(RecoveredMethod {
            structured: self,
            synthetic_semaphores: processor.synthetic_semaphores,
        })
    }

    /// Runs the expression pass on the current statement tree. Finally analysis
    /// calls this before assigning versions, and may later rebuild the tree.
    pub fn process_expressions(&mut self, cx: &mut Cx, class: &StructClass) -> io::Result<()> {
        let method = Arc::clone(self.root.method(&cx.ir));
        expr_processor::process_statement(
            cx,
            &mut self.flow.counters,
            self.root,
            class,
            &method,
            &self.descriptor,
        )
    }
}

fn structure_root(cx: &mut Cx, counters: &mut CounterContainer, root: StatId) -> io::Result<()> {
    if !process_statement(&mut cx.ir, counters, root, cx.options.try_loop_fix) {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "parsing failure!",
        ));
    }
    finish(cx, counters, root);
    Ok(())
}

impl InitialMethod {
    pub fn structure(mut self, cx: &mut Cx) -> io::Result<StructuredMethod> {
        structure_root(cx, &mut self.flow.counters, self.root)?;
        let method = self.root.method(&cx.ir);
        let mut descriptor = MethodDescriptor::parse_descriptor(&method.descriptor);
        if let Some(signature) = method.shared_signature() {
            descriptor.add_generic_descriptor(Arc::clone(signature));
        }
        Ok(StructuredMethod {
            descriptor: Arc::new(descriptor),
            flow: self.flow,
            root: self.root,
        })
    }
}

pub fn structured_statement_graph(
    cx: &mut Cx,
    class: &StructClass,
    method: &Arc<StructMethod>,
) -> io::Result<Option<StructuredMethod>> {
    initial_statement_graph(cx, class, method)?
        .map(|method| method.structure(cx))
        .transpose()
}

/// The stable tree after finally recovery and the synthetic locals introduced by it.
pub struct RecoveredMethod {
    pub structured: StructuredMethod,
    pub synthetic_semaphores: IndexSet<i32>,
}

/// Method state passed on to stack simplification after the final expression lift.
pub struct ExpressionMethod {
    pub flow: MethodGraph,
    pub root: StatId,
    pub descriptor: Arc<MethodDescriptor>,
    pub synthetic_semaphores: IndexSet<i32>,
}

impl RecoveredMethod {
    /// Removing the synchronized handlers consumes the recovered statement tree.
    pub fn into_expressions(
        mut self,
        cx: &mut Cx,
        class: &StructClass,
    ) -> io::Result<ExpressionMethod> {
        let method = &mut self.structured;
        prepare_expressions(cx, &mut method.flow.counters, method.root);
        method.process_expressions(cx, class)?;
        condense_sequences(cx, &mut method.flow.counters, method.root);
        Ok(ExpressionMethod {
            flow: self.structured.flow,
            root: self.structured.root,
            descriptor: self.structured.descriptor,
            synthetic_semaphores: self.synthetic_semaphores,
        })
    }
}

pub fn expression_method(
    cx: &mut Cx,
    class: &StructClass,
    method: &Arc<StructMethod>,
) -> io::Result<Option<ExpressionMethod>> {
    let Some(structured) = structured_statement_graph(cx, class, method)? else {
        return Ok(None);
    };
    structured
        .recover_finally(cx, class)?
        .into_expressions(cx, class)
        .map(Some)
}
