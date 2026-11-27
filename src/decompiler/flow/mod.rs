//! The direct graph used for expression and variable data flow.

pub mod flatten;

use crate::decompiler::ir::{Expr, ExprId, ExprListId, Ir, IrNode, StatId};
use crate::decompiler::stats::StatementKind;
use arcstr::ArcStr;
use index_vec::{IndexBox, IndexVec, define_index_type};
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;
use std::collections::VecDeque;
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

impl DirectEdgeType {
    fn successor_slot(self) -> usize {
        self as usize
    }

    fn predecessor_slot(self) -> usize {
        2 + self as usize
    }
}

pub struct DirectNode {
    pub id: ArcStr,
    pub ty: NodeType,
    pub stat: StatId,
    pub block: Option<StatId>,
    pub exprents: ExprListId,
    pub try_finally: Option<DirectId>,
    // Regular successors, exceptional successors, regular predecessors, and
    // exceptional predecessors occupy consecutive ranges in this buffer.
    edges: SmallVec<[DirectId; 4]>,
    edge_ends: [usize; 3],
}

impl DirectNode {
    pub fn successors(&self, kind: DirectEdgeType) -> &[DirectId] {
        self.edge_list(kind.successor_slot())
    }

    pub fn predecessors(&self, kind: DirectEdgeType) -> &[DirectId] {
        self.edge_list(kind.predecessor_slot())
    }

    fn edge_range(&self, slot: usize) -> std::ops::Range<usize> {
        let start = self.edge_ends[..slot].last().copied().unwrap_or(0);
        let end = self
            .edge_ends
            .get(slot)
            .copied()
            .unwrap_or(self.edges.len());
        start..end
    }

    fn edge_list(&self, slot: usize) -> &[DirectId] {
        &self.edges[self.edge_range(slot)]
    }

    fn add_edge(&mut self, slot: usize, node: DirectId) {
        self.edges.insert(self.edge_range(slot).end, node);
        for end in &mut self.edge_ends[slot..] {
            *end += 1;
        }
    }
}

pub struct DirectGraph {
    nodes: IndexBox<DirectId, [DirectNode]>,
    /// Upstream's `nodes` after sortReversePostOrder, including non-exit
    /// unreachable nodes prepended for SSA. Handles remain stable across sorting.
    pub order: Vec<DirectId>,
    pub extra_nodes: Vec<DirectId>,
    pub first: DirectId,
    pub neg_if_branch: FxHashMap<DirectId, DirectId>,
    destinations: FxHashMap<StatId, DirectId>,
    continue_destinations: FxHashMap<StatId, DirectId>,
}

impl DirectGraph {
    pub(crate) fn visit_ir_roots(&self, visit: &mut impl FnMut(IrNode)) {
        // Cached graphs can own lists with no corresponding statement list.
        // Include exception-only nodes and nodes omitted from traversal order.
        for node in self.nodes.iter() {
            visit(node.stat.into());
            if let Some(block) = node.block {
                visit(block.into());
            }
            visit(node.exprents.into());
        }
        for &stat in self
            .destinations
            .keys()
            .chain(self.continue_destinations.keys())
        {
            visit(stat.into());
        }
    }

    /// Regular BFS followed by Exprent.getAllExprents(true, true) within each
    /// list. Callers may reuse this order while the expression tree is stable.
    pub(crate) fn deep_exprents(&self, ir: &Ir) -> Vec<ExprId> {
        let mut order = Vec::new();
        for node in self.regular_breadth_first() {
            for &expr in &ir[self[node].exprents] {
                Expr::append_exprents(ir, expr, true, &mut order);
                order.push(expr);
            }
        }
        order
    }

    pub fn direct_node(&self, stat: StatId) -> Option<DirectId> {
        self.destinations.get(&stat).copied()
    }

    /// The direct node reached by a continue targeting this statement.
    pub fn continue_node(&self, stat: StatId) -> Option<DirectId> {
        self.continue_destinations.get(&stat).copied()
    }

    /// The node order of `DirectGraph.iterateExprents`. The ordered regular
    /// edges determine which equal direct node is reached first.
    pub fn regular_breadth_first(&self) -> impl Iterator<Item = DirectId> + '_ {
        let mut seen = FxHashSet::default();
        seen.insert(&self[self.first].id);
        let mut pending = VecDeque::from([self.first]);
        std::iter::from_fn(move || {
            let node = pending.pop_front()?;
            pending.extend(
                self[node]
                    .successors(DirectEdgeType::Regular)
                    .iter()
                    .copied()
                    .filter(|&id| seen.insert(&self[id].id)),
            );
            Some(node)
        })
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
            edges: SmallVec::new(),
            edge_ends: [0; 3],
        })
    }

    pub fn connect(&mut self, source: DirectId, dest: DirectId, kind: DirectEdgeType) {
        // DirectNode.equals compares the generated name and node kind. Names
        // include the kind suffix, including when two allocations represent it.
        for (node, neighbor, slot) in [
            (source, dest, kind.successor_slot()),
            (dest, source, kind.predecessor_slot()),
        ] {
            if !self[node]
                .edge_list(slot)
                .iter()
                .any(|&existing| self[existing].id == self[neighbor].id)
            {
                self.nodes[node].add_edge(slot, neighbor);
            }
        }
    }

    pub fn finish(
        self,
        ir: &Ir,
        first: DirectId,
        destinations: FxHashMap<StatId, DirectId>,
        continue_destinations: FxHashMap<StatId, DirectId>,
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
                    && !matches!(ir[node.stat].kind, StatementKind::DummyExit { .. }))
                .then_some(id)
            })
            .collect();
        order.extend(extra_nodes.iter().copied());
        order.reverse();
        DirectGraph {
            nodes: self.nodes.into_boxed_slice(),
            first,
            order,
            extra_nodes,
            neg_if_branch: self.neg_if_branch,
            destinations,
            continue_destinations,
        }
    }
}
