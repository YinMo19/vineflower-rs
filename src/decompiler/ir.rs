// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Arenas and handles of the statement / expression IR.
//!
//! Upstream's statements, edges, expressions and basic blocks form a mutable
//! object graph with cycles, aliasing and identity comparisons. Here every
//! live object keeps its handle when the worker reclaims unreachable graphs.
//! A `Copy` handle stands for the Java reference: two handles
//! are equal exactly when the references were identical, and a change made
//! through one alias is visible through all others.
//!
//! The methods of upstream's base classes are methods of the handles, taking
//! the arenas (or the whole context, when they need more) first:
//! `stat.add_successor(ir, edge)`. Fields are reached by indexing:
//! `ir[stat].first`.

use std::ops::{Index, IndexMut};

use index_vec::define_index_type;

mod arena;
mod reachable;

pub use arena::Arena;
use arena::Marks;

pub use super::exps::{Expr, ExprKind};
use super::stats::{Statement, stat_edge::StatEdge};
use super::vars::processor::VarProcessor;
use crate::code::cfg::basic_block::BasicBlock;

macro_rules! arenas {
    ($( $(#[$doc:meta])* $id:ident($variant:ident): $field:ident => $object:ty, )+) => {
        $( define_index_type! { $(#[$doc])* pub struct $id = u32; } )+

        #[derive(Default)]
        pub struct Ir {
            $( pub $field: Arena<$id, $object>, )+
        }

        #[derive(Clone, Copy)]
        pub(crate) enum IrNode {
            $( $variant($id), )+
        }

        #[derive(Default)]
        pub(crate) struct LiveNodes {
            $( $field: Marks, )+
        }

        impl LiveNodes {
            fn insert(&mut self, node: IrNode) -> bool {
                match node { $( IrNode::$variant(id) => self.$field.insert(id), )+ }
            }

            pub(crate) fn contains(&self, node: IrNode) -> bool {
                match node { $( IrNode::$variant(id) => self.$field.contains(id), )+ }
            }
        }

        impl Ir {
            /// Create an empty worker IR that can later return its pages to this coordinator.
            pub(crate) fn fork(&mut self) -> Self {
                Self { $( $field: self.$field.fork(), )+ }
            }

            /// Take ownership of a worker's nodes without changing their handles.
            pub(crate) fn adopt(&mut self, worker: Self) {
                $( self.$field.adopt(worker.$field); )+
            }

            pub(crate) fn allocated_bytes(&self) -> u64 {
                0 $( + self.$field.allocated_bytes() )+
            }

            pub(crate) fn sweep(&mut self, live: &LiveNodes) -> u64 {
                0 $( + self.$field.sweep(&live.$field) )+
            }
        }

        $(
            impl From<$id> for IrNode {
                fn from(id: $id) -> Self { Self::$variant(id) }
            }

            impl Index<$id> for Ir {
                type Output = $object;
                fn index(&self, id: $id) -> &$object { &self.$field[id] }
            }

            impl IndexMut<$id> for Ir {
                fn index_mut(&mut self, id: $id) -> &mut $object { &mut self.$field[id] }
            }
        )+
    };
}

arenas! {
    /// A reference to a `Statement`.
    StatId(Stat): stats => Statement,
    /// A reference to a `StatEdge`.
    EdgeId(Edge): edges => StatEdge,
    /// A reference to an `Exprent`.
    ExprId(Expr): exprs => Expr,
    /// A list shared by statements and flattened graph nodes.
    ExprListId(List): lists => Vec<ExprId>,
    /// A reference to a `BasicBlock`.
    BlockId(Block): blocks => BasicBlock,
    /// The variable processor shared by all local expressions of one method.
    VarProcessorId(VarProcessor): variable_processors => VarProcessor,
}

impl Ir {
    /// `new ArrayList<>(exprents)` stored where other owners can reach it.
    pub fn new_list(&mut self, exprents: Vec<ExprId>) -> ExprListId {
        self.lists.push(exprents)
    }

    pub(crate) fn reachable(&self, mut pending: Vec<IrNode>) -> LiveNodes {
        let mut live = LiveNodes::default();
        while let Some(node) = pending.pop() {
            if live.insert(node) {
                reachable::visit_children(self, node, |child| pending.push(child));
            }
        }
        live
    }
}
