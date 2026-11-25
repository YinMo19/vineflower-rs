// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! The state upstream reaches through the thread-local `DecompilerContext`,
//! passed explicitly as `cx` instead.

use std::sync::Arc;

use super::import_collector::ImportCollector;
use super::options::Options;
use crate::decompiler::ir::Ir;
use crate::renamer::pool_interceptor::PoolInterceptor;
use crate::structs::StructContext;

/// Everything a translated function may consult or update while classes are
/// being decompiled by one worker.
pub struct Cx {
    /// `DecompilerContext.getOption` and friends.
    pub options: Arc<Options>,
    /// `DecompilerContext.getStructContext()`.
    pub struct_context: Arc<StructContext>,
    /// `DecompilerContext.getPoolInterceptor()`.
    pub pool_interceptor: Option<Arc<PoolInterceptor>>,
    /// Object identities shared by methods and nested classes in this root class.
    pub ir: Ir,
    /// `DecompilerContext.getImportCollector()`.
    pub imports: ImportCollector,
}

impl Cx {
    /// Creates the worker state for processing a root class against a registered class path.
    pub fn new(struct_context: Arc<StructContext>) -> Self {
        Self {
            options: Arc::clone(struct_context.options()),
            pool_interceptor: struct_context.pool_interceptor().cloned(),
            struct_context,
            imports: ImportCollector::default(),
            ir: Ir::default(),
        }
    }
}
