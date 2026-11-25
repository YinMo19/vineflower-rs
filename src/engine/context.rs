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
use crate::decompiler::ir::Ir;
use crate::renamer::pool_interceptor::PoolInterceptor;
use crate::structs::StructContext;
use crate::structs::struct_context::ClassResolver;

/// Everything a translated function may consult or update while classes are
/// being decompiled by one worker.
pub struct Cx {
    /// `DecompilerContext.getOption` and friends.
    pub options: Arc<Options>,
    /// `DecompilerContext.getStructContext()`.
    pub struct_context: Arc<StructContext>,
    pub(crate) expression_ids: ExpressionIds,
    /// `DecompilerContext.getPoolInterceptor()`.
    pub pool_interceptor: Option<Arc<PoolInterceptor>>,
    /// Object identities shared by methods and nested classes in this root class.
    pub ir: Ir,
    /// ClassesProcessor.mapRootClasses in this root-class worker.
    pub class_nodes: ClassNodes,
    /// ClassNode currently used for import shadowing.
    pub current_class_node: Option<arcstr::ArcStr>,
    /// `DecompilerContext.getImportCollector()`.
    pub imports: ImportCollector,
}

impl Cx {
    /// Creates the worker state for processing a root class against a registered class path.
    pub fn new(struct_context: Arc<StructContext>) -> Self {
        Self {
            options: Arc::clone(struct_context.options()),
            pool_interceptor: struct_context.pool_interceptor().cloned(),
            expression_ids: struct_context.metadata_ids().clone(),
            struct_context,
            class_nodes: ClassNodes::default(),
            current_class_node: None,
            imports: ImportCollector::default(),
            ir: Ir::default(),
        }
    }

    pub(crate) fn classes(&self) -> ClassResolver<'_> {
        self.struct_context.resolving_with(&self.expression_ids)
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
