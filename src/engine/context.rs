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
use crate::decompiler::ir::{Ir, VarProcessorId};
use crate::renamer::pool_interceptor::PoolInterceptor;
use crate::structs::struct_context::ClassResolver;
use crate::structs::{StructContext, StructMethod};

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
    /// Object identities shared by methods and nested classes in this root class.
    pub ir: Ir,
    /// ClassesProcessor.mapRootClasses in this root-class worker.
    pub class_nodes: ClassNodes,
    /// ClassNode currently used for import shadowing.
    pub current_class_node: Option<arcstr::ArcStr>,
    /// Lambda call sites can share their declaring class and even their
    /// synthetic name. Preserve the exact node while running inside ClassWriter.
    current_node_id: Option<super::class_nodes::ClassNodeId>,
    /// `DecompilerContext.getImportCollector()`.
    pub imports: ImportCollector,
    pub source_mapper: super::bytecode_source_mapper::BytecodeSourceMapper,
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
            current_class_node: None,
            current_node_id: None,
            imports: ImportCollector::default(),
            source_mapper: Default::default(),
            ir: Ir::default(),
        }
    }

    pub(crate) fn classes(&self) -> ClassResolver<'_> {
        self.struct_context.resolving_with(&self.expression_ids)
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
