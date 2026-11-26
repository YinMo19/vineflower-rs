// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! The state upstream reaches through the thread-local `DecompilerContext`,
//! passed explicitly as `cx` instead.

use std::ops::{Deref, DerefMut};
use std::sync::Arc;

use super::class_nodes::ClassNodes;
use super::counter_container::{CounterContainer, ExpressionIds};
use super::import_collector::ImportCollector;
use super::options::Options;
use crate::code::method_properties::MethodProperties;
use crate::decompiler::ir::{Ir, IrNode, VarProcessorId};
use crate::renamer::pool_interceptor::PoolInterceptor;
use crate::structs::struct_context::ClassResolver;
use crate::structs::{StructClass, StructContext, StructMethod};

/// Everything a translated function may consult or update while classes are
/// being decompiled by one worker.
pub struct Cx {
    /// `DecompilerContext.getOption` and friends.
    pub options: Arc<Options>,
    /// `DecompilerContext.getStructContext()`.
    pub struct_context: Arc<StructContext>,
    pub(crate) current_method_wrapper: Option<super::class_wrapper::MethodSlot>,
    pub(crate) current_method: Option<(Arc<StructMethod>, VarProcessorId)>,
    pub(crate) expression_ids: ExpressionIds,
    /// `DecompilerContext.getPoolInterceptor()`.
    pub pool_interceptor: Option<Arc<PoolInterceptor>>,
    /// Optional documentation supplied by the embedding application.
    pub javadoc: Option<Arc<dyn super::class_writer::javadoc::JavadocProvider>>,
    /// Stable handles shared by all methods and classes processed by this worker.
    pub ir: Ir,
    /// Prepared method graphs returned by workers for the root currently being initialized.
    pub(super) prepared_methods: Option<Box<super::method_processor::PreparedMethods>>,
    pub(crate) kotlin_body: Option<Box<crate::kotlin::body::KotlinBody>>,
    /// ClassesProcessor.mapRootClasses in this root-class worker.
    pub class_nodes: ClassNodes,
    /// Kotlin attributes shared across this decompilation session.
    pub(crate) kotlin_members: Option<Box<crate::kotlin::members::KotlinMembers>>,
    /// CURRENT_CLASS remains the last initialized wrapper during source writing.
    pub(crate) current_class: Option<Arc<StructClass>>,
    /// ClassNode currently used for import shadowing.
    pub current_class_node: Option<arcstr::ArcStr>,
    /// Lambda call sites can share their declaring class and even their
    /// synthetic name. Preserve the exact node while running inside ClassWriter.
    current_node_id: Option<super::class_nodes::ClassNodeId>,
    /// `DecompilerContext.getImportCollector()`.
    pub imports: ImportCollector,
    pub source_mapper: super::bytecode_source_mapper::BytecodeSourceMapper,
}

// Imports and counters are per class while the wrapper arena is shared.
pub(super) struct ClassSession {
    current_method_wrapper: Option<super::class_wrapper::MethodSlot>,
    current_method: Option<(Arc<StructMethod>, VarProcessorId)>,
    expression_ids: ExpressionIds,
    current_class: Option<Arc<StructClass>>,
    current_class_node: Option<arcstr::ArcStr>,
    current_node_id: Option<super::class_nodes::ClassNodeId>,
    imports: ImportCollector,
    source_mapper: super::bytecode_source_mapper::BytecodeSourceMapper,
}

impl Cx {
    /// Creates the worker state for processing a root class against a registered class path.
    pub fn new(struct_context: Arc<StructContext>) -> Self {
        Self {
            options: Arc::clone(struct_context.options()),
            pool_interceptor: struct_context.pool_interceptor().cloned(),
            current_method_wrapper: None,
            javadoc: None,
            current_method: None,
            expression_ids: struct_context.metadata_ids().clone(),
            struct_context,
            class_nodes: ClassNodes::default(),
            kotlin_members: None,
            current_class: None,
            current_class_node: None,
            current_node_id: None,
            imports: ImportCollector::default(),
            source_mapper: Default::default(),
            ir: Ir::default(),
            prepared_methods: None,
            kotlin_body: None,
        }
    }

    /// Take one class's ambient state, leaving shared wrappers and expressions in place.
    pub(super) fn take_class_session(&mut self) -> ClassSession {
        ClassSession {
            current_method_wrapper: self.current_method_wrapper.take(),
            current_method: self.current_method.take(),
            expression_ids: std::mem::take(&mut self.expression_ids),
            current_class: self.current_class.take(),
            current_class_node: self.current_class_node.take(),
            current_node_id: self.current_node_id.take(),
            imports: std::mem::take(&mut self.imports),
            source_mapper: std::mem::take(&mut self.source_mapper),
        }
    }

    pub(super) fn restore_class_session(&mut self, session: ClassSession) {
        self.current_method_wrapper = session.current_method_wrapper;
        self.current_method = session.current_method;
        self.expression_ids = session.expression_ids;
        self.current_class = session.current_class;
        self.current_class_node = session.current_class_node;
        self.current_node_id = session.current_node_id;
        self.imports = session.imports;
        self.source_mapper = session.source_mapper;
    }

    /// At a driver phase boundary no pass holds a temporary graph. Published
    /// wrappers, class nodes and saved method scopes own all remaining handles.
    pub(super) fn reclaim_ir<'a>(
        &mut self,
        sessions: impl Iterator<Item = &'a ClassSession>,
    ) -> u64 {
        let mut roots = Vec::<IrNode>::new();
        self.class_nodes.visit_ir_roots(|node| roots.push(node));
        for (_, variables) in sessions
            .filter_map(|session| session.current_method.as_ref())
            .chain(self.current_method.as_ref())
        {
            roots.push((*variables).into());
        }
        let live = self.ir.trace_published(roots);
        if let Some(body) = &mut self.kotlin_body {
            body.retain_ir_nodes(|node| live.contains(node));
        }
        self.ir.sweep(&live)
    }

    pub(crate) fn classes(&self) -> ClassResolver<'_> {
        self.class_nodes.require_class_session();
        self.struct_context.resolving_with(&self.expression_ids)
    }

    pub(crate) fn method_properties<'a>(
        &self,
        class: &'a StructClass,
        key: &str,
    ) -> Option<&'a MethodProperties> {
        // A failed read leaves the worker's OnceLock initialization unfinished.
        // The coordinator reads and reports it in class wrapper order.
        class.method_properties_with(key, || self.class_nodes.require_class_session())
    }

    pub fn kotlin_members(&self) -> Option<&crate::kotlin::members::KotlinMembers> {
        self.kotlin_members.as_deref()
    }

    pub(crate) fn current_node(&self) -> Option<super::class_nodes::ClassNodeId> {
        self.current_node_id
            .or_else(|| self.class_nodes.id(self.current_class_node.as_deref()?))
    }

    /// Imports and type names resolve against the class currently being written.
    pub(crate) fn with_class_node<T>(
        &mut self,
        node: super::class_nodes::ClassNodeId,
        write: impl FnOnce(&mut Cx) -> T,
    ) -> T {
        struct ClassScope<'a> {
            cx: &'a mut Cx,
            previous: Option<arcstr::ArcStr>,
            previous_id: Option<super::class_nodes::ClassNodeId>,
        }
        impl Drop for ClassScope<'_> {
            fn drop(&mut self) {
                self.cx.current_class_node = self.previous.take();
                self.cx.current_node_id = self.previous_id;
            }
        }
        let previous = self
            .current_class_node
            .replace(self.class_nodes[node].class.qualified_name.clone());
        let previous_id = self.current_node_id.replace(node);
        write(
            ClassScope {
                cx: self,
                previous,
                previous_id,
            }
            .cx,
        )
    }

    /// Allow lookups during speculative rendering without adding imports.
    pub(crate) fn with_locked_imports<T>(&mut self, render: impl FnOnce(&mut Cx) -> T) -> T {
        struct ImportLock<'a> {
            cx: &'a mut Cx,
            previously_locked: bool,
        }

        impl Drop for ImportLock<'_> {
            fn drop(&mut self) {
                self.cx.imports.set_write_locked(self.previously_locked);
            }
        }

        let previously_locked = self.imports.set_write_locked(true);
        let lock = ImportLock {
            cx: self,
            previously_locked,
        };
        render(lock.cx)
    }

    /// Library metadata first read during this pass uses the active method's
    /// expression counter. Restore the enclosing worker scope on every exit.
    pub(crate) fn enter_method(&mut self, counters: &CounterContainer) -> MethodScope<'_> {
        let previous = std::mem::replace(&mut self.expression_ids, counters.expressions.clone());
        MethodScope { cx: self, previous }
    }
}

pub(crate) struct MethodScope<'a> {
    cx: &'a mut Cx,
    previous: ExpressionIds,
}

impl Deref for MethodScope<'_> {
    type Target = Cx;

    fn deref(&self) -> &Cx {
        self.cx
    }
}

impl DerefMut for MethodScope<'_> {
    fn deref_mut(&mut self) -> &mut Cx {
        self.cx
    }
}

impl Drop for MethodScope<'_> {
    fn drop(&mut self) {
        std::mem::swap(&mut self.cx.expression_ids, &mut self.previous);
    }
}
