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

pub use super::exps::{Expr, ExprKind};
use super::stats::{Statement, stat_edge::StatEdge};
use super::vars::processor::VarProcessor;
use crate::code::cfg::basic_block::BasicBlock;

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

define_index_type! {
    /// The variable processor shared by all local expressions of one method.
    pub struct VarProcessorId = u32;
}

#[derive(Default)]
pub struct Ir {
    pub variable_processors: IndexVec<VarProcessorId, VarProcessor>,
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
    variable_processors: VarProcessorId => VarProcessor,
    stats: StatId => Statement,
    edges: EdgeId => StatEdge,
    exprs: ExprId => Expr,
    lists: ExprListId => Vec<ExprId>,
    blocks: BlockId => BasicBlock,
}
