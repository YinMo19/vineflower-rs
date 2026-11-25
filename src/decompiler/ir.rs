// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Arenas and handles of the statement / expression IR.
//!
//! Upstream's statements, edges, expressions and basic blocks form a mutable
//! object graph with cycles, aliasing and identity comparisons. Here every
//! such object lives in an arena for as long as its root class is being
//! decompiled, and a `Copy` handle stands for the Java reference: two handles
//! are equal exactly when the references were identical, and a change made
//! through one alias is visible through all others.
//!
//! The methods of upstream's base classes are methods of the handles, taking
//! the arenas (or the whole context, when they need more) first:
//! `stat.add_successor(ir, edge)`. Fields are reached by indexing:
//! `ir[stat].first`.

use std::ops::{Index, IndexMut};

use index_vec::{IndexVec, define_index_type};

use super::stats::{Statement, stat_edge::StatEdge};
use crate::code::cfg::basic_block::BasicBlock;
use crate::engine::counter_container::{CounterContainer, EXPRESSION_COUNTER, VAR_COUNTER};
use crate::types::VarType;

define_index_type! {
    /// A reference to a `Statement`.
    pub struct StatId = u32;
}

define_index_type! {
    /// A reference to a `StatEdge`.
    pub struct EdgeId = u32;
}

define_index_type! {
    /// A reference to an `Exprent`.
    pub struct ExprId = u32;
}

define_index_type! {
    /// A reference to a `List<Exprent>` object that statements and flattened
    /// graph nodes share.
    pub struct ExprListId = u32;
}

define_index_type! {
    /// A reference to a `BasicBlock`.
    pub struct BlockId = u32;
}

/// The expressions created when structuring catch handlers and switch cases.
#[derive(Clone, Debug)]
pub struct Expr {
    pub id: i32,
    pub kind: ExprKind,
    pub var_type: VarType,
}

#[derive(Clone, Debug)]
pub enum ExprKind {
    IntConstant { value: i32, bool_permitted: bool },
    Variable { index: i32 },
}

impl Expr {
    pub fn new_int_constant(
        ir: &mut Ir,
        counters: &mut CounterContainer,
        value: i32,
        bool_permitted: bool,
    ) -> ExprId {
        let var_type = match value {
            0 | 1 if bool_permitted => VarType::VARTYPE_BOOLEAN,
            0..=127 => VarType::VARTYPE_BYTECHAR,
            -128..=-1 => VarType::VARTYPE_BYTE,
            128..=32767 => VarType::VARTYPE_SHORTCHAR,
            -32768..=-129 => VarType::VARTYPE_SHORT,
            32768..=65535 => VarType::VARTYPE_CHAR,
            _ => VarType::VARTYPE_INT,
        };
        ir.exprs.push(Self {
            id: counters.get_counter_and_increment(EXPRESSION_COUNTER),
            kind: ExprKind::IntConstant {
                value,
                bool_permitted,
            },
            var_type,
        })
    }

    pub fn new_variable(ir: &mut Ir, counters: &mut CounterContainer, var_type: VarType) -> ExprId {
        let index = counters.get_counter_and_increment(VAR_COUNTER);
        ir.exprs.push(Self {
            id: counters.get_counter_and_increment(EXPRESSION_COUNTER),
            kind: ExprKind::Variable { index },
            var_type,
        })
    }
}

#[derive(Default)]
pub struct Ir {
    pub stats: IndexVec<StatId, Statement>,
    pub edges: IndexVec<EdgeId, StatEdge>,
    pub exprs: IndexVec<ExprId, Expr>,
    pub lists: IndexVec<ExprListId, Vec<ExprId>>,
    pub blocks: IndexVec<BlockId, BasicBlock>,
}

impl Ir {
    /// `new ArrayList<>(exprents)` stored where other owners can reach it.
    pub fn new_list(&mut self, exprents: Vec<ExprId>) -> ExprListId {
        self.lists.push(exprents)
    }
}

macro_rules! arena_index {
    ($($field:ident: $id:ty => $node:ty,)*) => {$(
        impl Index<$id> for Ir {
            type Output = $node;

            fn index(&self, id: $id) -> &$node {
                &self.$field[id]
            }
        }

        impl IndexMut<$id> for Ir {
            fn index_mut(&mut self, id: $id) -> &mut $node {
                &mut self.$field[id]
            }
        }
    )*};
}

arena_index! {
    stats: StatId => Statement,
    edges: EdgeId => StatEdge,
    exprs: ExprId => Expr,
    lists: ExprListId => Vec<ExprId>,
    blocks: BlockId => BasicBlock,
}
