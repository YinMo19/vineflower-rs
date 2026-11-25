// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! `main.collectors.CounterContainer`: the per-method id counters whose
//! values surface in the output as label numbers and variable names.

pub const STATEMENT_COUNTER: usize = 0;
pub const EXPRESSION_COUNTER: usize = 1;
pub const VAR_COUNTER: usize = 2;
pub const DOT_FILE_COUNTER: usize = 3;

#[derive(Clone, Debug)]
pub struct CounterContainer {
    values: [i32; 4],
}

impl Default for CounterContainer {
    fn default() -> Self {
        Self { values: [1; 4] }
    }
}

impl CounterContainer {
    pub fn set_counter(&mut self, counter: usize, value: i32) {
        self.values[counter] = value;
    }

    pub fn get_counter(&self, counter: usize) -> i32 {
        self.values[counter]
    }

    pub fn get_counter_and_increment(&mut self, counter: usize) -> i32 {
        let value = self.values[counter];
        self.values[counter] += 1;
        value
    }
}
