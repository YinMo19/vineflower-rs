// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! `util.token`: the ranges of generated source that name a class, field,
//! method or variable, and `main.extern.TextTokenVisitor`, which receives them.
//!
//! Positions and lengths count UTF-16 units, like the buffer they refer to.

use crate::types::{FieldDescriptor, MethodDescriptor};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TextRange {
    pub start: i32,
    pub length: i32,
}

impl TextRange {
    pub fn end(&self) -> i32 {
        self.start + self.length
    }
}

#[derive(Clone, Debug)]
pub struct TextToken {
    pub start: i32,
    pub length: i32,
    pub declaration: bool,
    pub kind: TokenKind,
}

/// The subclass of a token: `ClassTextToken`, `FieldTextToken`,
/// `MethodTextToken` or `VariableTextToken`.
#[derive(Clone, Debug)]
pub enum TokenKind {
    Class {
        qualified_name: String,
    },
    Field {
        class_name: String,
        name: String,
        descriptor: FieldDescriptor,
    },
    Method {
        class_name: String,
        name: String,
        descriptor: MethodDescriptor,
    },
    Variable {
        parameter: bool,
        class_name: String,
        method_name: String,
        method_descriptor: MethodDescriptor,
        index: i32,
        name: String,
    },
}

impl TextToken {
    pub fn new(start: i32, length: i32, declaration: bool, kind: TokenKind) -> Self {
        Self {
            start,
            length,
            declaration,
            kind,
        }
    }

    pub fn shift(&mut self, amount: i32) {
        self.start += amount;
    }

    pub fn visit(&self, visitor: &mut dyn TextTokenVisitor) {
        let range = TextRange {
            start: self.start,
            length: self.length,
        };
        match &self.kind {
            TokenKind::Class { qualified_name } => {
                visitor.visit_class(range, self.declaration, qualified_name)
            }
            TokenKind::Field {
                class_name,
                name,
                descriptor,
            } => visitor.visit_field(range, self.declaration, class_name, name, descriptor),
            TokenKind::Method {
                class_name,
                name,
                descriptor,
            } => visitor.visit_method(range, self.declaration, class_name, name, descriptor),
            TokenKind::Variable {
                parameter,
                class_name,
                method_name,
                method_descriptor,
                index,
                name,
            } => {
                let variable = VariableToken {
                    declaration: self.declaration,
                    class_name,
                    method_name,
                    method_descriptor,
                    index: *index,
                    name,
                };
                if *parameter {
                    visitor.visit_parameter(range, variable);
                } else {
                    visitor.visit_local(range, variable);
                }
            }
        }
    }
}

/// What `visitParameter` and `visitLocal` are told about a variable.
#[derive(Clone, Copy, Debug)]
pub struct VariableToken<'a> {
    pub declaration: bool,
    pub class_name: &'a str,
    pub method_name: &'a str,
    pub method_descriptor: &'a MethodDescriptor,
    pub index: i32,
    pub name: &'a str,
}

/// `main.extern.TextTokenVisitor`. Upstream chains visitors through a `next`
/// field; here a visitor that wraps another forwards to it itself.
pub trait TextTokenVisitor {
    fn start(&mut self, _content: &str) {}

    fn visit_class(&mut self, _range: TextRange, _declaration: bool, _name: &str) {}

    fn visit_field(
        &mut self,
        _range: TextRange,
        _declaration: bool,
        _class_name: &str,
        _name: &str,
        _descriptor: &FieldDescriptor,
    ) {
    }

    fn visit_method(
        &mut self,
        _range: TextRange,
        _declaration: bool,
        _class_name: &str,
        _name: &str,
        _descriptor: &MethodDescriptor,
    ) {
    }

    fn visit_parameter(&mut self, _range: TextRange, _variable: VariableToken<'_>) {}

    fn visit_local(&mut self, _range: TextRange, _variable: VariableToken<'_>) {}

    fn end(&mut self) {}
}
