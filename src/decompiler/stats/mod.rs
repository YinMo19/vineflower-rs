// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! `modules.decompiler.stats.Statement` variants and the
//! operations shared by statements in a control-flow graph.

pub mod recognize;
pub mod rewrite;
pub mod stat_edge;
pub mod write;

use std::sync::Arc;

use arcstr::ArcStr;
use indexmap::IndexSet;
use rustc_hash::FxHashMap;

use self::stat_edge::EdgeType;
use crate::code::cfg::ControlFlowGraph;
use crate::code::cfg::basic_block::BasicBlock;
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
    General {
        placeholder: bool,
    },
    Do(DoStatement),
    Switch(SwitchStatement),
    If(IfStatement),
    Sequence,
    Catch {
        exceptions: Vec<Vec<ArcStr>>,
        vars: Vec<ExprId>,
        resources: Option<ExprListId>,
    },
    CatchAll {
        handler: Option<StatId>,
        is_finally: bool,
        monitor: Option<ExprId>,
        vars: Vec<ExprId>,
    },
    Synchronized {
        body: StatId,
        head_exprents: Option<ExprListId>,
    },
    Root {
        method: Arc<StructMethod>,
        dummy_exit: StatId,
        comment_lines: Option<IndexSet<String>>,
        add_error_comment: bool,
        content_flags: ContentFlags,
    },
    DummyExit {
        bytecode: Option<crate::decompiler::exps::BytecodeOffsets>,
    },
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ContentFlags {
    pub has_try_catch: bool,
    pub has_loops: bool,
    pub has_switch: bool,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum LoopType {
    #[default]
    Infinite,
    While,
    DoWhile,
    For,
    ForEach,
}

#[derive(Clone, Copy, Debug, Default)]
pub struct DoStatement {
    pub ty: LoopType,
    // An unallocated slot and an empty list both represent a null expression.
    // Once allocated, a list keeps its identity as its expression changes.
    pub init: Option<ExprListId>,
    pub condition: Option<ExprListId>,
    pub increment: Option<ExprListId>,
}

impl DoStatement {
    pub fn init(self, ir: &Ir) -> Option<ExprId> {
        self.init.and_then(|list| ir[list].first().copied())
    }

    pub fn condition(self, ir: &Ir) -> Option<ExprId> {
        self.condition.and_then(|list| ir[list].first().copied())
    }

    pub fn increment(self, ir: &Ir) -> Option<ExprId> {
        self.increment.and_then(|list| ir[list].first().copied())
    }
}

#[derive(Clone, Copy, Default)]
pub struct IfStatement {
    pub has_else: bool,
    pub negated: bool,
    pub pattern_matched: bool,
    pub has_ppmm: bool,
    pub if_stat: Option<StatId>,
    pub else_stat: Option<StatId>,
    pub if_edge: Option<EdgeId>,
    pub else_edge: Option<EdgeId>,
    pub head_exprents: Option<ExprListId>,
}

#[derive(Clone, Default)]
pub struct SwitchStatement {
    pub scoped_case_statements: rustc_hash::FxHashSet<StatId>,
    pub default_edge: Option<EdgeId>,
    pub cases: Vec<SwitchCase>,
    /// Labels still owned by the header after terminal case bodies were hidden.
    trailing_case_values: Vec<Vec<Option<ExprId>>>,
    /// Indexed by case. Cases beyond the end of the list have no guard.
    pub case_guards: Vec<Option<ExprId>>,
    pub head_exprents: Option<ExprListId>,
}

impl SwitchStatement {
    pub(crate) fn case_values_mut(&mut self) -> impl Iterator<Item = &mut [Option<ExprId>]> {
        self.cases
            .iter_mut()
            .map(|case| case.values.as_mut_slice())
            .chain(self.trailing_case_values.iter_mut().map(Vec::as_mut_slice))
    }

    pub fn case_values(&self) -> impl Iterator<Item = &[Option<ExprId>]> {
        self.cases
            .iter()
            .map(|case| case.values.as_slice())
            .chain(self.trailing_case_values.iter().map(Vec::as_slice))
    }

    /// Detach the terminal default edge from the case table alone.
    pub(crate) fn remove_trailing_default(&mut self) {
        let last = self.cases.last_mut().expect("Missing terminal case");
        if let Some(index) = last
            .edges
            .iter()
            .position(|&edge| Some(edge) == self.default_edge)
        {
            last.edges.remove(index);
        }
        if last.edges.is_empty() {
            self.trailing_case_values
                .insert(0, self.cases.pop().unwrap().values);
        }
    }
}

#[derive(Clone)]
pub struct SwitchCase {
    pub statement: StatId,
    pub edges: Vec<EdgeId>,
    /// The default label has no expression. Hiding its edge retains the value.
    pub values: Vec<Option<ExprId>>,
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
    pub removable_monitorexit: bool,
    pub copied: bool,
    pub phantom: bool,
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
            removable_monitorexit: false,
            copied: false,
            phantom: false,
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

    pub fn new_empty_basic_block(ir: &mut Ir, counters: &mut CounterContainer) -> StatId {
        let id = counters.get_counter_and_increment(STATEMENT_COUNTER);
        let block = BasicBlock::new(ir, id);
        let stat = Self::new_basic_block(ir, counters, block);
        ir[stat].exprents = Some(ir.new_list(Vec::new()));
        stat
    }

    pub fn new_sequence(
        ir: &mut Ir,
        counters: &mut CounterContainer,
        children: &[StatId],
    ) -> StatId {
        let id = counters.get_counter_and_increment(STATEMENT_COUNTER);
        let mut statement = Self::new(StatementKind::Sequence, id);
        statement.first = Some(children[0]);
        statement.last_basic_type = ir[*children.last().unwrap()].last_basic_type;
        for &child in children {
            statement.stats.add_with_key(child, ir[child].id);
        }
        ir.stats.push(statement)
    }

    pub fn new_general(
        ir: &mut Ir,
        counters: &mut CounterContainer,
        head: StatId,
        statements: impl IntoIterator<Item = StatId>,
        post: Option<StatId>,
    ) -> StatId {
        let id = counters.get_counter_and_increment(STATEMENT_COUNTER);
        let mut statement = Self::new(StatementKind::General { placeholder: false }, id);
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
                content_flags: ContentFlags::default(),
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
        ir.stats
            .push(Self::new(StatementKind::DummyExit { bytecode: None }, id))
    }

    pub fn new_synchronized(
        ir: &mut Ir,
        counters: &mut CounterContainer,
        head: StatId,
        body: StatId,
        handler: StatId,
    ) -> StatId {
        let id = counters.get_counter_and_increment(STATEMENT_COUNTER);
        let mut statement = Self::new(
            StatementKind::Synchronized {
                body,
                head_exprents: None,
            },
            id,
        );
        statement.first = Some(head);
        for child in [head, body, handler] {
            statement.stats.add_with_key(child, ir[child].id);
        }
        if let Some(&edge) = ir[body]
            .edge_view(EdgeDirection::Forward, STATEDGE_DIRECT_ALL)
            .first()
            && ir[edge].edge_type == EdgeType::Regular
        {
            statement.post = Some(ir[edge].destination);
        }
        ir.stats.push(statement)
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

    pub fn all_successors(&self) -> &[EdgeId] {
        self.edge_view(EdgeDirection::Forward, STATEDGE_ALL)
    }

    pub fn all_predecessors(&self) -> &[EdgeId] {
        self.edge_view(EdgeDirection::Backward, STATEDGE_ALL)
    }

    pub(crate) fn indexed_edges(&self) -> impl Iterator<Item = EdgeId> + '_ {
        self.successor_edges
            .values()
            .chain(self.predecessor_edges.values())
            .flatten()
            .copied()
    }

    pub fn direct_successors(&self) -> &[EdgeId] {
        self.edge_view(EdgeDirection::Forward, STATEDGE_DIRECT_ALL)
    }

    pub fn first_successor(&self) -> Option<EdgeId> {
        self.all_successors().first().copied()
    }

    pub(crate) fn has_basic_succ_edge(&self) -> bool {
        match self.kind {
            StatementKind::BasicBlock { .. } | StatementKind::If(IfStatement { has_else: false, .. }) => true,
            StatementKind::Do(header) => header.ty != LoopType::Infinite,
            _ => false,
        }
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
        self.add_comments(graph.comment_lines.iter().cloned(), graph.add_error_comment);
    }

    pub fn add_comment(&mut self, text: &str, error: bool) {
        self.add_comments([text.to_owned()], error);
    }

    fn add_comments(&mut self, comments: impl IntoIterator<Item = String>, error: bool) {
        let StatementKind::Root {
            comment_lines,
            add_error_comment,
            ..
        } = &mut self.kind
        else {
            panic!("Only root statements carry comments");
        };
        for comment in comments {
            comment_lines
                .get_or_insert_with(IndexSet::new)
                .insert(comment);
        }
        *add_error_comment |= error;
    }

    pub(crate) fn clear_temp_information(&mut self) {
        self.post = None;
        self.continue_set = IndexSet::new();
        self.copied = false;
        self.is_monitor_enter = false;
        self.contains_monitor_exit = false;

        // Copy the direct view into the all-edge view. These are index changes;
        // the edge objects and the statement's remaining metadata stay live.
        for index in [&mut self.successor_edges, &mut self.predecessor_edges] {
            index.remove(&EdgeType::Exception.mask());
            if let Some(direct) = index.get(&STATEDGE_DIRECT_ALL).cloned() {
                index.insert(STATEDGE_ALL, direct);
            } else {
                index.remove(&STATEDGE_ALL);
            }
        }
    }
}

impl StatId {
    pub fn set_loop_type(self, ir: &mut Ir, ty: LoopType) {
        let StatementKind::Do(loop_stat) = &mut ir.stats[self].kind else {
            panic!("Only loop statements have a loop type");
        };
        loop_stat.ty = ty;
        if ty != LoopType::Infinite {
            // Materialize the three lists once the loop has a header.
            for slot in [
                &mut loop_stat.init,
                &mut loop_stat.condition,
                &mut loop_stat.increment,
            ] {
                slot.get_or_insert_with(|| ir.lists.push(Vec::new()));
            }
        }
    }

    pub fn set_loop_init(self, ir: &mut Ir, expr: ExprId) {
        self.set_loop_exprent(ir, |loop_stat| &mut loop_stat.init, expr);
    }

    pub fn set_loop_condition(self, ir: &mut Ir, expr: ExprId) {
        self.set_loop_exprent(ir, |loop_stat| &mut loop_stat.condition, expr);
    }

    pub fn set_loop_increment(self, ir: &mut Ir, expr: ExprId) {
        self.set_loop_exprent(ir, |loop_stat| &mut loop_stat.increment, expr);
    }

    fn set_loop_exprent(
        self,
        ir: &mut Ir,
        slot: impl FnOnce(&mut DoStatement) -> &mut Option<ExprListId>,
        expr: ExprId,
    ) {
        let StatementKind::Do(loop_stat) = &mut ir.stats[self].kind else {
            panic!("Only loop statements have loop headers");
        };
        let list = *slot(loop_stat).get_or_insert_with(|| ir.lists.push(Vec::new()));
        let list = &mut ir[list];
        if let Some(first) = list.first_mut() {
            *first = expr;
        } else {
            list.push(expr);
        }
    }

    pub fn method(self, ir: &Ir) -> &Arc<StructMethod> {
        let StatementKind::Root { method, .. } = &ir[self].kind else {
            unreachable!("Only the root owns the method")
        };
        method
    }

    /// Append the previous root's comments when finally processing reparses the CFG.
    pub fn add_comments_from(self, ir: &mut Ir, previous: StatId) {
        let StatementKind::Root {
            comment_lines,
            add_error_comment,
            ..
        } = &ir[previous].kind
        else {
            panic!("Comments must come from a root statement");
        };
        let previous_comments = comment_lines.clone();
        let previous_error = *add_error_comment;
        ir[self].add_comments(previous_comments.into_iter().flatten(), previous_error);
    }

    pub fn build_content_flags(self, ir: &mut Ir) {
        let StatementKind::Root {
            mut content_flags, ..
        } = ir[self].kind
        else {
            panic!("Only root statements carry content flags");
        };
        let mut pending = vec![self];
        while let Some(stat) = pending.pop() {
            match ir[stat].kind {
                StatementKind::Catch { .. } | StatementKind::CatchAll { .. } => {
                    content_flags.has_try_catch = true;
                }
                StatementKind::Do(_) => content_flags.has_loops = true,
                StatementKind::Switch(_) => content_flags.has_switch = true,
                _ => {}
            }
            pending.extend(ir[stat].stats.iter().copied());
        }
        let StatementKind::Root {
            content_flags: flags,
            ..
        } = &mut ir[self].kind
        else {
            unreachable!();
        };
        *flags = content_flags;
    }

    pub fn is_placeholder(self, ir: &Ir) -> bool {
        matches!(ir[self].kind, StatementKind::General { placeholder: true })
    }

    pub fn set_placeholder(self, ir: &mut Ir) {
        let StatementKind::General { placeholder } = &mut ir[self].kind else {
            panic!("Only general statements can be placeholders");
        };
        *placeholder = true;
    }

    pub fn add_successor(self, ir: &mut Ir, edge: EdgeId) {
        debug_assert_eq!(self, ir[edge].source);
        let destination = ir[edge].destination;
        self.add_edge_internal(ir, EdgeDirection::Forward, edge);
        if let Some(closure) = ir[edge].closure {
            ir[closure].label_edges.insert(edge);
        }
        destination.add_edge_internal(ir, EdgeDirection::Backward, edge);
    }

    /// Detach the predecessor entry while discarding an entire source subtree.
    pub(crate) fn remove_predecessor(self, ir: &mut Ir, edge: EdgeId) {
        debug_assert_eq!(self, ir[edge].destination);
        self.remove_edge_internal(ir, EdgeDirection::Backward, edge);
    }

    pub fn remove_successor(self, ir: &mut Ir, edge: EdgeId) {
        // Java removes from the receiver's forward index. During rewrites the
        // receiver can already have replaced a detached source statement.
        self.remove_edge_internal(ir, EdgeDirection::Forward, edge);
        if let Some(closure) = ir[edge].closure {
            ir[closure].label_edges.shift_remove(&edge);
        }
        ir[edge].destination.remove_predecessor(ir, edge);
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
        if matches!(ir[self].kind, StatementKind::Do(_)) {
            continues.shift_remove(&ir[self].first.unwrap().get_basic_head(ir));
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
            StatementKind::Root { .. }
            | StatementKind::General { .. }
            | StatementKind::Synchronized { .. } => {}
            _ => {
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

impl StatId {
    /// Install a Kotlin subclass with the fields copied by its constructor.
    /// The original remains in the arena for references the JVM constructors
    /// leave alone, such as the parent held by an already wrapped child.
    pub(crate) fn replace_with_kotlin(
        self,
        ir: &mut Ir,
        counters: &mut CounterContainer,
    ) -> Option<StatId> {
        let copy_list = |ir: &mut Ir, list: Option<ExprListId>| {
            list.map(|list| ir.new_list(ir[list].clone()))
        };
        let kind = match &ir[self].kind {
            StatementKind::Sequence => StatementKind::Sequence,
            StatementKind::Do(data) => {
                let mut data = *data;
                data.init = copy_list(ir, data.init);
                data.condition = copy_list(ir, data.condition);
                data.increment = copy_list(ir, data.increment);
                StatementKind::Do(data)
            }
            StatementKind::If(data) => {
                let mut data = *data;
                data.head_exprents = copy_list(ir, data.head_exprents);
                StatementKind::If(data)
            }
            StatementKind::Switch(data) => {
                let mut data = data.clone();
                data.scoped_case_statements.clear();
                data.head_exprents = copy_list(ir, data.head_exprents);
                StatementKind::Switch(data)
            }
            StatementKind::Catch {
                exceptions,
                vars,
                resources,
            } => {
                let (exceptions, vars, resources) = (exceptions.clone(), vars.clone(), *resources);
                StatementKind::Catch {
                    exceptions,
                    vars,
                    resources: copy_list(ir, resources),
                }
            }
            _ => return None,
        };
        let original = &ir[self];
        let mut replacement =
            Statement::new(kind, counters.get_counter_and_increment(STATEMENT_COUNTER));
        replacement.stats = original.stats.clone();
        replacement.first = original.first;
        replacement.parent = original.parent;
        replacement.exprents = original.exprents;
        replacement.label_edges = original.label_edges.clone();
        replacement.var_definitions = original.var_definitions.clone();
        replacement.post = original.post;
        replacement.last_basic_type = original.last_basic_type;
        replacement.is_monitor_enter = original.is_monitor_enter;
        replacement.contains_monitor_exit = original.contains_monitor_exit;
        replacement.is_last_athrow = original.is_last_athrow && !original.contains_monitor_exit;
        replacement.continue_set = original.continue_set.clone();
        replacement.phantom = matches!(replacement.kind, StatementKind::Switch(_)) && original.phantom;
        let replacement = ir.stats.push(replacement);

        if let StatementKind::Switch(switch) = &ir[replacement].kind {
            let head = switch.head_exprents;
            let share_cases = !recognize::can_sort_switch(ir, replacement);
            recognize::init_simple_copy(ir, counters, replacement);
            if share_cases
                && let Some(expr) = head.and_then(|list| ir[list].first().copied())
                && let crate::decompiler::exps::ExprKind::SwitchHead {
                    case_values: Some(crate::decompiler::exps::SwitchCaseValues::Statement(owner)),
                    ..
                } = &mut ir[expr].kind
                && *owner == self
            {
                // Both switches copy the outer table of case lists. The head
                // still sees the original inner lists when sorting is skipped.
                *owner = replacement;
            }
        }
        self.replace_with(ir, replacement);
        Some(replacement)
    }
}
