// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! `code.ExceptionHandler` and `code.ExceptionTable`: the exception handlers
//! of a method, with their ranges in instruction indices.

use arcstr::ArcStr;

use crate::engine::Cx;

/// The handler protects the instructions `from..to`; `to` is the number of
/// instructions when the range runs to the end of the method.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ExceptionHandler {
    pub from: i32,
    pub to: i32,
    pub handler: i32,
    /// The internal name of the caught class; `None` catches everything.
    pub exception_class: Option<ArcStr>,
}

impl ExceptionHandler {
    pub fn to_string(&self, cx: &Cx) -> String {
        let new_line_separator = cx.options.line_separator();
        format!(
            "from instr: {} to instr: {} handler instr: {}{new_line_separator}\
             exception class: {}{new_line_separator}",
            self.from,
            self.to,
            self.handler,
            self.exception_class.as_deref().unwrap_or("null"),
        )
    }
}

#[derive(Clone, Debug, Default)]
pub struct ExceptionTable {
    pub handlers: Vec<ExceptionHandler>,
}

impl ExceptionTable {
    pub const EMPTY: ExceptionTable = ExceptionTable::new(Vec::new());

    pub const fn new(handlers: Vec<ExceptionHandler>) -> Self {
        Self { handlers }
    }
}
