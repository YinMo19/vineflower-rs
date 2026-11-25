// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Initial variants of `modules.decompiler.stats.Statement` and the
//! operations shared by statements in a control-flow graph.

pub mod stat_edge;

use std::sync::Arc;

use indexmap::IndexSet;
use rustc_hash::FxHashMap;

use self::stat_edge::EdgeType;
use crate::code::cfg::ControlFlowGraph;
use crate::code::code_constants::{
    GROUP_JUMP, GROUP_SWITCH, OPC_ATHROW, OPC_GOTO, OPC_MONITORENTER, OPC_MONITOREXIT,
};
use crate::decompiler::ir::{BlockId, EdgeId, ExprId, ExprListId, Ir, StatId};
use crate::engine::counter_container::{CounterContainer, STATEMENT_COUNTER};
use crate::structs::StructMethod;
use crate::util::vb_style_collection::VBStyleCollection;

pub const STATEDGE_ALL: u32 = 0x80000000;
pub const STATEDGE_DIRECT_ALL: u32 = 0x40000000;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EdgeDirection {
    Backward,
    Forward,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum LastBasicType {
    If,
    Switch,
    #[default]
    General,
}

pub enum StatementKind {
    BasicBlock {
        block: BlockId,
    },
    General,
    Root {
        method: Arc<StructMethod>,
        dummy_exit: StatId,
        comment_lines: Option<IndexSet<String>>,
        add_error_comment: bool,
    },
    DummyExit,
}

pub struct Statement {
    pub id: i32,
    pub kind: StatementKind,
    pub stats: VBStyleCollection<StatId, i32>,
    pub first: Option<StatId>,
    pub parent: Option<StatId>,
    pub post: Option<StatId>,
    pub last_basic_type: LastBasicType,
    pub is_monitor_enter: bool,
    pub is_last_athrow: bool,
    pub contains_monitor_exit: bool,
    pub continue_set: IndexSet<StatId>,
    pub label_edges: IndexSet<EdgeId>,
    pub exprents: Option<ExprListId>,
    pub var_definitions: Vec<ExprId>,
    successor_edges: FxHashMap<u32, Vec<EdgeId>>,
    predecessor_edges: FxHashMap<u32, Vec<EdgeId>>,
}

impl Statement {
    fn new(kind: StatementKind, id: i32) -> Self {
        Self {
            id,
            kind,
            stats: VBStyleCollection::new(),
            first: None,
            parent: None,
            post: None,
            last_basic_type: LastBasicType::General,
            is_monitor_enter: false,
            is_last_athrow: false,
            contains_monitor_exit: false,
            continue_set: IndexSet::new(),
            label_edges: IndexSet::new(),
            exprents: None,
            var_definitions: Vec::new(),
            successor_edges: FxHashMap::default(),
            predecessor_edges: FxHashMap::default(),
        }
    }

    pub fn new_basic_block(ir: &mut Ir, counters: &mut CounterContainer, block: BlockId) -> StatId {
        let id = ir[block].id;
        if id >= counters.get_counter(STATEMENT_COUNTER) {
            counters.set_counter(STATEMENT_COUNTER, id + 1);
        }

        let mut statement = Self::new(StatementKind::BasicBlock { block }, id);
        if let Some(instr) = ir[block].get_last_instruction() {
            if instr.group == GROUP_JUMP && instr.opcode != OPC_GOTO {
                statement.last_basic_type = LastBasicType::If;
            } else if instr.group == GROUP_SWITCH {
                statement.last_basic_type = LastBasicType::Switch;
            }
        }

        let stat = ir.stats.push(statement);
        stat.build_monitor_flags(ir);
        stat
    }

    pub fn new_general(
        ir: &mut Ir,
        counters: &mut CounterContainer,
        head: StatId,
        statements: impl IntoIterator<Item = StatId>,
        post: Option<StatId>,
    ) -> StatId {
        let id = counters.get_counter_and_increment(STATEMENT_COUNTER);
        let mut statement = Self::new(StatementKind::General, id);
        statement.first = Some(head);
        statement.post = post;
        statement.stats.add_with_key(head, ir[head].id);
        let children: IndexSet<_> = statements
            .into_iter()
            .filter(|&stat| stat != head)
            .collect();
        for child in children {
            statement.stats.add_with_key(child, ir[child].id);
        }
        // Upstream sets the children's parent when the general statement is collapsed.
        ir.stats.push(statement)
    }

    pub fn new_root(
        ir: &mut Ir,
        counters: &mut CounterContainer,
        head: StatId,
        dummy_exit: StatId,
        method: Arc<StructMethod>,
    ) -> StatId {
        let id = counters.get_counter_and_increment(STATEMENT_COUNTER);
        let mut statement = Self::new(
            StatementKind::Root {
                method,
                dummy_exit,
                comment_lines: None,
                add_error_comment: false,
            },
            id,
        );
        statement.first = Some(head);
        statement.stats.add_with_key(head, ir[head].id);
        let root = ir.stats.push(statement);
        ir[head].parent = Some(root);
        root
    }

    pub fn new_dummy_exit(ir: &mut Ir, counters: &mut CounterContainer) -> StatId {
        let id = counters.get_counter_and_increment(STATEMENT_COUNTER);
        ir.stats.push(Self::new(StatementKind::DummyExit, id))
    }

    fn edge_index(&self, direction: EdgeDirection) -> &FxHashMap<u32, Vec<EdgeId>> {
        match direction {
            EdgeDirection::Backward => &self.predecessor_edges,
            EdgeDirection::Forward => &self.successor_edges,
        }
    }

    fn edge_index_mut(&mut self, direction: EdgeDirection) -> &mut FxHashMap<u32, Vec<EdgeId>> {
        match direction {
            EdgeDirection::Backward => &mut self.predecessor_edges,
            EdgeDirection::Forward => &mut self.successor_edges,
        }
    }

    fn edge_view(&self, direction: EdgeDirection, mask: u32) -> &[EdgeId] {
        self.edge_index(direction)
            .get(&mask)
            .map_or(&[], Vec::as_slice)
    }

    pub(super) fn add_edge_to_index(&mut self, direction: EdgeDirection, mask: u32, edge: EdgeId) {
        self.edge_index_mut(direction)
            .entry(mask)
            .or_default()
            .push(edge);
    }

    pub(super) fn remove_edge_from_index(
        &mut self,
        direction: EdgeDirection,
        mask: u32,
        edge: EdgeId,
    ) {
        if let Some(edges) = self.edge_index_mut(direction).get_mut(&mask)
            && let Some(index) = edges.iter().position(|&entry| entry == edge)
        {
            edges.remove(index);
        }
    }

    pub fn contains_monitor_exit_or_athrow(&self) -> bool {
        self.contains_monitor_exit || self.is_last_athrow
    }

    /// The comments transferred at the start of `DomHelper.parseGraph`.
    pub fn add_graph_comments(&mut self, graph: &ControlFlowGraph) {
        let StatementKind::Root {
            comment_lines,
            add_error_comment,
            ..
        } = &mut self.kind
        else {
            panic!("Only root statements carry graph comments");
        };
        if !graph.comment_lines.is_empty() {
            comment_lines
                .get_or_insert_with(IndexSet::new)
                .extend(graph.comment_lines.iter().cloned());
        }
        *add_error_comment |= graph.add_error_comment;
    }
}

impl StatId {
    pub fn add_successor(self, ir: &mut Ir, edge: EdgeId) {
        debug_assert_eq!(self, ir[edge].source);
        let destination = ir[edge].destination;
        self.add_edge_internal(ir, EdgeDirection::Forward, edge);
        if let Some(closure) = ir[edge].closure {
            ir[closure].label_edges.insert(edge);
        }
        destination.add_edge_internal(ir, EdgeDirection::Backward, edge);
    }

    pub fn remove_successor(self, ir: &mut Ir, edge: EdgeId) {
        debug_assert_eq!(self, ir[edge].source);
        edge.remove(ir);
    }

    pub fn add_labeled_edge(self, ir: &mut Ir, edge: EdgeId) {
        edge.change_closure(ir, Some(self));
    }

    fn add_edge_internal(self, ir: &mut Ir, direction: EdgeDirection, edge: EdgeId) {
        let kind = ir[edge].edge_type;
        ir[self].add_edge_to_index(direction, kind.mask(), edge);
        ir[self].add_edge_to_index(direction, STATEDGE_ALL, edge);
        if kind != EdgeType::Exception {
            ir[self].add_edge_to_index(direction, STATEDGE_DIRECT_ALL, edge);
        }
    }

    fn remove_edge_internal(self, ir: &mut Ir, direction: EdgeDirection, edge: EdgeId) {
        let kind = ir[edge].edge_type;
        ir[self].remove_edge_from_index(direction, kind.mask(), edge);
        ir[self].remove_edge_from_index(direction, STATEDGE_ALL, edge);
        if kind != EdgeType::Exception {
            ir[self].remove_edge_from_index(direction, STATEDGE_DIRECT_ALL, edge);
        }
    }

    /// Single masks retain insertion order, and combined type masks follow
    /// the order in `StatEdge.TYPES` upstream.
    pub fn get_edges(self, ir: &Ir, mask: u32, direction: EdgeDirection) -> Vec<EdgeId> {
        if mask.count_ones() <= 1 {
            return ir[self].edge_view(direction, mask).to_vec();
        }
        EdgeType::TYPES
            .into_iter()
            .filter(|kind| mask & kind.mask() != 0)
            .flat_map(|kind| ir[self].edge_view(direction, kind.mask()).iter().copied())
            .collect()
    }

    pub fn get_successor_edges(self, ir: &Ir, mask: u32) -> Vec<EdgeId> {
        self.get_edges(ir, mask, EdgeDirection::Forward)
    }

    pub fn get_predecessor_edges(self, ir: &Ir, mask: u32) -> Vec<EdgeId> {
        self.get_edges(ir, mask, EdgeDirection::Backward)
    }

    pub fn get_neighbours(self, ir: &Ir, mask: u32, direction: EdgeDirection) -> Vec<StatId> {
        self.get_edges(ir, mask, direction)
            .into_iter()
            .map(|edge| match direction {
                EdgeDirection::Backward => ir[edge].source,
                EdgeDirection::Forward => ir[edge].destination,
            })
            .collect()
    }

    pub fn get_basic_head(self, ir: &Ir) -> StatId {
        let mut head = self;
        while !matches!(ir[head].kind, StatementKind::BasicBlock { .. }) {
            head = ir[head].first.expect("Statement has no basic head");
        }
        head
    }

    pub fn set_all_parent(self, ir: &mut Ir) {
        for index in 0..ir[self].stats.len() {
            let child = ir[self].stats[index];
            ir[child].parent = Some(self);
        }
    }

    pub fn is_labeled(self, ir: &Ir) -> bool {
        ir[self]
            .label_edges
            .iter()
            .any(|&edge| ir[edge].labeled && ir[edge].explicit)
    }

    pub fn build_continue_set(self, ir: &mut Ir) {
        let mut continues = std::mem::take(&mut ir[self].continue_set);
        continues.clear();
        for index in 0..ir[self].stats.len() {
            let child = ir[self].stats[index];
            child.build_continue_set(ir);
            continues.extend(ir[child].continue_set.iter().copied());
            if Some(child) != ir[self].first {
                continues.shift_remove(&child.get_basic_head(ir));
            }
        }
        for &edge in ir[self].edge_view(EdgeDirection::Forward, EdgeType::Continue.mask()) {
            continues.insert(ir[edge].destination.get_basic_head(ir));
        }
        ir[self].continue_set = continues;
    }

    pub fn build_monitor_flags(self, ir: &mut Ir) {
        for index in 0..ir[self].stats.len() {
            ir[self].stats[index].build_monitor_flags(ir);
        }

        match ir[self].kind {
            StatementKind::BasicBlock { block } => {
                let block = &ir[block];
                if let Some(last) = block.get_last_instruction() {
                    let last_opcode = last.opcode;
                    let contains_monitor_exit = block
                        .seq
                        .iter()
                        .any(|instr| instr.opcode == OPC_MONITOREXIT);
                    ir[self].contains_monitor_exit |= contains_monitor_exit;
                    ir[self].is_monitor_enter = last_opcode == OPC_MONITORENTER;
                    ir[self].is_last_athrow = last_opcode == OPC_ATHROW;
                }
            }
            StatementKind::Root { .. } | StatementKind::General => {}
            StatementKind::DummyExit => {
                ir[self].contains_monitor_exit = ir[self]
                    .stats
                    .iter()
                    .any(|&stat| ir[stat].contains_monitor_exit);
                ir[self].is_last_athrow =
                    ir[self].stats.iter().any(|&stat| ir[stat].is_last_athrow);
            }
        }
    }
}
