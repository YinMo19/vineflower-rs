// Copyright 2000-2024 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! The direct graph used for expression and variable data flow.

pub mod flatten;

use crate::decompiler::ir::{ExprListId, Ir, StatId};
use crate::decompiler::stats::StatementKind;
use arcstr::ArcStr;
use index_vec::{IndexVec, define_index_type};
use rustc_hash::{FxHashMap, FxHashSet};
use std::ops::Index;

define_index_type! { pub struct DirectId = u32; }

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum NodeType {
    Direct,
    Tail,
    Init,
    Condition,
    Increment,
    Try,
    Catch,
    CombinedCatch,
    Finally,
    FinallyEnd,
    ForeachVardef,
    Case,
}

impl NodeType {
    fn make_id(self, stat: i32) -> ArcStr {
        let suffix = match self {
            Self::Direct => return stat.to_string().into(),
            Self::Tail => "tail",
            Self::Init => "init",
            Self::Condition => "condition",
            Self::Increment => "increment",
            Self::Try => "try",
            Self::Catch => "catch",
            Self::CombinedCatch => "combined_catch",
            Self::Finally => "finally",
            Self::FinallyEnd => "finally_end",
            Self::ForeachVardef => "foreach_vardef",
            Self::Case => "case",
        };
        format!("{stat}_{suffix}").into()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DirectEdgeType {
    Regular,
    Exception,
}

pub struct DirectNode {
    pub id: ArcStr,
    pub ty: NodeType,
    pub stat: StatId,
    pub block: Option<StatId>,
    pub exprents: ExprListId,
    pub try_finally: Option<DirectId>,
    successors: [Vec<DirectId>; 2],
    predecessors: [Vec<DirectId>; 2],
}

impl DirectNode {
    pub fn successors(&self, kind: DirectEdgeType) -> &[DirectId] {
        &self.successors[kind as usize]
    }
    pub fn predecessors(&self, kind: DirectEdgeType) -> &[DirectId] {
        &self.predecessors[kind as usize]
    }
}

pub struct DirectGraph {
    nodes: IndexVec<DirectId, DirectNode>,
    /// Upstream's `nodes` after sortReversePostOrder, including non-exit
    /// unreachable nodes prepended for SSA. Handles remain stable across sorting.
    pub order: Vec<DirectId>,
    pub extra_nodes: Vec<DirectId>,
    pub first: DirectId,
    pub neg_if_branch: FxHashMap<DirectId, DirectId>,
    destinations: FxHashMap<StatId, DirectId>,
}

impl DirectGraph {
    pub fn direct_node(&self, stat: StatId) -> Option<DirectId> {
        self.destinations.get(&stat).copied()
    }
}

#[derive(Default)]
pub(crate) struct DirectGraphBuilder {
    nodes: IndexVec<DirectId, DirectNode>,
    pub neg_if_branch: FxHashMap<DirectId, DirectId>,
}

macro_rules! index_direct_node {
    ($ty:ty) => {
        impl Index<DirectId> for $ty {
            type Output = DirectNode;
            fn index(&self, id: DirectId) -> &DirectNode {
                &self.nodes[id]
            }
        }
    };
}
index_direct_node!(DirectGraph);
index_direct_node!(DirectGraphBuilder);

impl DirectGraphBuilder {
    pub fn add_node(
        &mut self,
        ir: &mut Ir,
        stat: StatId,
        ty: NodeType,
        exprents: Option<ExprListId>,
        try_finally: Option<DirectId>,
    ) -> DirectId {
        let block = (ty == NodeType::Direct
            && matches!(ir[stat].kind, StatementKind::BasicBlock { .. }))
        .then_some(stat);
        self.nodes.push(DirectNode {
            id: ty.make_id(ir[stat].id),
            ty,
            stat,
            block,
            exprents: exprents.unwrap_or_else(|| ir.new_list(Vec::new())),
            try_finally,
            successors: Default::default(),
            predecessors: Default::default(),
        })
    }

    pub fn connect(&mut self, source: DirectId, dest: DirectId, kind: DirectEdgeType) {
        // DirectNode.equals compares the generated name and node kind. Names
        // include the kind suffix, including when two allocations represent it.
        if !self[source]
            .successors(kind)
            .iter()
            .any(|&succ| self[succ].id == self[dest].id)
        {
            self.nodes[source].successors[kind as usize].push(dest);
        }
        if !self[dest]
            .predecessors(kind)
            .iter()
            .any(|&pred| self[pred].id == self[source].id)
        {
            self.nodes[dest].predecessors[kind as usize].push(source);
        }
    }

    pub fn finish(
        self,
        ir: &Ir,
        first: DirectId,
        destinations: FxHashMap<StatId, DirectId>,
    ) -> DirectGraph {
        let mut visited = FxHashSet::default();
        visited.insert(&self[first].id);
        let mut stack = vec![(first, 0)];
        let mut order = Vec::with_capacity(self.nodes.len());
        while let Some((id, index)) = stack.last_mut() {
            if let Some(&next) = self[*id].successors(DirectEdgeType::Regular).get(*index) {
                *index += 1;
                if visited.insert(&self[next].id) {
                    stack.push((next, 0));
                }
            } else {
                order.push(stack.pop().unwrap().0);
            }
        }

        // DirectNode.hashCode includes the JVM enum object's identity. Visit
        // unreachable nodes in creation order, then prepend as upstream does.
        let extra_nodes: Vec<_> = self
            .nodes
            .iter_enumerated()
            .filter_map(|(id, node)| {
                (visited.insert(&node.id)
                    && !matches!(ir[node.stat].kind, StatementKind::DummyExit))
                .then_some(id)
            })
            .collect();
        order.extend(extra_nodes.iter().copied());
        order.reverse();
        DirectGraph {
            nodes: self.nodes,
            first,
            order,
            extra_nodes,
            neg_if_branch: self.neg_if_branch,
            destinations,
        }
    }
}
