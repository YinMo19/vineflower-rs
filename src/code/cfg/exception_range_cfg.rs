// Copyright 2000-2020 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! `code.cfg.ExceptionRangeCFG`: a handler and the blocks it protects.

use arcstr::ArcStr;
use itertools::Itertools;

use crate::decompiler::ir::BlockId;

#[derive(Clone, Debug)]
pub struct ExceptionRangeCFG {
    pub protected_range: Vec<BlockId>,
    pub handler: BlockId,
    /// `None` catches every exception.
    pub exception_types: Option<Vec<ArcStr>>,
}

impl ExceptionRangeCFG {
    pub fn new(
        protected_range: Vec<BlockId>,
        handler: BlockId,
        exception_types: Option<Vec<ArcStr>>,
    ) -> Self {
        Self {
            protected_range,
            handler,
            exception_types,
        }
    }

    pub fn is_circular(&self) -> bool {
        self.protected_range.contains(&self.handler)
    }

    pub fn add_exception_type(&mut self, exception_type: Option<ArcStr>) {
        match exception_type {
            Some(class) => {
                if let Some(types) = &mut self.exception_types {
                    types.push(class);
                }
            }
            None => self.exception_types = None,
        }
    }

    pub fn get_unique_exceptions_string(&self) -> Option<String> {
        self.exception_types
            .as_ref()
            .map(|types| types.iter().map(ArcStr::as_str).unique().join(":"))
    }
}

impl ExceptionRangeCFG {
    pub(super) fn protects(&self, handler: BlockId, block: BlockId) -> bool {
        self.handler == handler && self.protected_range.contains(&block)
    }
}
