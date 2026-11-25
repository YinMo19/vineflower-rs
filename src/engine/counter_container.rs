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

/// Method expressions and annotation expressions constructed by a nested
/// class read take IDs from the same sequence.
#[derive(Clone, Debug)]
pub(crate) struct ExpressionIds(Arc<AtomicI32>);

impl Default for ExpressionIds {
    fn default() -> Self {
        Self(Arc::new(AtomicI32::new(1)))
    }
}

impl ExpressionIds {
    pub(crate) fn next(&self) -> i32 {
        self.0.fetch_add(1, Ordering::Relaxed)
    }

    fn value(&self) -> i32 {
        self.0.load(Ordering::Relaxed)
    }
}

#[derive(Debug)]
pub struct CounterContainer {
    statements: i32,
    pub(crate) expressions: ExpressionIds,
    variables: i32,
    dot_files: i32,
}

impl Default for CounterContainer {
    fn default() -> Self {
        Self {
            statements: 1,
            expressions: ExpressionIds::default(),
            variables: 1,
            dot_files: 1,
        }
    }
}

impl Clone for CounterContainer {
    fn clone(&self) -> Self {
        Self {
            statements: self.statements,
            expressions: ExpressionIds(Arc::new(AtomicI32::new(self.expressions.value()))),
            variables: self.variables,
            dot_files: self.dot_files,
        }
    }
}

impl CounterContainer {
    pub fn set_counter(&mut self, counter: usize, value: i32) {
        match counter {
            STATEMENT_COUNTER => self.statements = value,
            EXPRESSION_COUNTER => self.expressions.0.store(value, Ordering::Relaxed),
            VAR_COUNTER => self.variables = value,
            DOT_FILE_COUNTER => self.dot_files = value,
            _ => panic!("Unknown counter {counter}"),
        }
    }

    pub fn get_counter(&self, counter: usize) -> i32 {
        match counter {
            STATEMENT_COUNTER => self.statements,
            EXPRESSION_COUNTER => self.expressions.value(),
            VAR_COUNTER => self.variables,
            DOT_FILE_COUNTER => self.dot_files,
            _ => panic!("Unknown counter {counter}"),
        }
    }

    pub fn get_counter_and_increment(&mut self, counter: usize) -> i32 {
        let scalar = match counter {
            STATEMENT_COUNTER => &mut self.statements,
            EXPRESSION_COUNTER => return self.expressions.next(),
            VAR_COUNTER => &mut self.variables,
            DOT_FILE_COUNTER => &mut self.dot_files,
            _ => panic!("Unknown counter {counter}"),
        };
        let value = *scalar;
        *scalar = value.wrapping_add(1);
        value
    }
}
