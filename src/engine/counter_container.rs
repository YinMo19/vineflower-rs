// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! `main.collectors.CounterContainer`: the per-method id counters whose
//! values surface in the output as label numbers and variable names.

use std::sync::{
    Arc,
    atomic::{AtomicI32, Ordering},
};

pub const STATEMENT_COUNTER: usize = 0;
pub const EXPRESSION_COUNTER: usize = 1;
pub const VAR_COUNTER: usize = 2;
pub const DOT_FILE_COUNTER: usize = 3;

/// A metadata reader can allocate expression IDs from the active method without
/// borrowing its decompiler graph. The four counters share the method's lifetime.
#[derive(Clone, Debug)]
pub(crate) struct ExpressionIds(Arc<[AtomicI32; 4]>);

impl Default for ExpressionIds {
    fn default() -> Self {
        Self(Arc::new(std::array::from_fn(|_| AtomicI32::new(1))))
    }
}

impl ExpressionIds {
    pub(crate) fn next(&self) -> i32 {
        self.0[EXPRESSION_COUNTER].fetch_add(1, Ordering::Relaxed)
    }
}

#[derive(Default, Debug)]
pub struct CounterContainer {
    pub(crate) expressions: ExpressionIds,
}

impl Clone for CounterContainer {
    /// An independent snapshot. A published wrapper explicitly shares the
    /// original sequence with its method body.
    fn clone(&self) -> Self {
        let values = std::array::from_fn(|i| AtomicI32::new(self.get_counter(i)));
        Self::with_expression_ids(ExpressionIds(Arc::new(values)))
    }
}

impl CounterContainer {
    pub(crate) fn with_expression_ids(expressions: ExpressionIds) -> Self {
        Self { expressions }
    }

    pub(crate) fn shared(&self) -> Self {
        Self::with_expression_ids(self.expressions.clone())
    }

    pub fn set_counter(&mut self, counter: usize, value: i32) {
        self.expressions.0[counter].store(value, Ordering::Relaxed);
    }

    pub fn get_counter(&self, counter: usize) -> i32 {
        self.expressions.0[counter].load(Ordering::Relaxed)
    }

    pub fn get_counter_and_increment(&mut self, counter: usize) -> i32 {
        self.expressions.0[counter].fetch_add(1, Ordering::Relaxed)
    }
}
