//! `FlattenStatementsHelper`: expand a structured statement into direct nodes.

use rustc_hash::FxHashMap;

use super::{DirectEdgeType, DirectGraph, DirectGraphBuilder, DirectId, NodeType};
use crate::decompiler::ir::{EdgeId, ExprListId, Ir, StatId};
use crate::decompiler::stats::stat_edge::EdgeType;
use crate::decompiler::stats::{
    DoStatement, IfStatement, LastBasicType, LoopType, STATEDGE_ALL, STATEDGE_DIRECT_ALL,
    StatementKind,
};
use crate::engine::method_timeout::checkpoint;

pub fn build_direct_graph(ir: &mut Ir, root: StatId) -> DirectGraph {
    let StatementKind::Root { dummy_exit, .. } = ir[root].kind else {
        panic!("A direct graph requires a root statement");
    };
    let mut flatten = Flatten::new(ir);
    let first = flatten.flatten_statement(root);
    let exit = flatten.create_node(dummy_exit, NodeType::Direct, None);
    flatten.regular_destinations.insert(dummy_exit, exit);
    flatten.resolve_edges();
    flatten.graph.finish(
        flatten.ir,
        first,
        flatten.regular_destinations,
        flatten.continue_destinations,
    )
}

struct DeferredEdge {
    source: DirectId,
    destination: StatId,
    kind: EdgeType,
}

struct Flatten<'a> {
    ir: &'a mut Ir,
    graph: DirectGraphBuilder,
    regular_destinations: FxHashMap<StatId, DirectId>,
    continue_destinations: FxHashMap<StatId, DirectId>,
    deferred_edges: Vec<DeferredEdge>,
    positive_if_branches: FxHashMap<DirectId, StatId>,
    try_nodes: Vec<Vec<DirectId>>,
    finally_nodes: Vec<DirectId>,
}

impl<'a> Flatten<'a> {
    fn new(ir: &'a mut Ir) -> Self {
        Self {
            ir,
            graph: DirectGraphBuilder::default(),
            regular_destinations: FxHashMap::default(),
            continue_destinations: FxHashMap::default(),
            deferred_edges: Vec::new(),
            positive_if_branches: FxHashMap::default(),
            try_nodes: Vec::new(),
            finally_nodes: Vec::new(),
        }
    }

    fn create_node(
        &mut self,
        stat: StatId,
        kind: NodeType,
        exprents: Option<ExprListId>,
    ) -> DirectId {
        let active_finally = self.finally_nodes.last().copied();
        let node = self
            .graph
            .add_node(self.ir, stat, kind, exprents, active_finally);
        if let Some(nodes) = self.try_nodes.last_mut() {
            nodes.push(node);
        }
        node
    }

    fn flatten_statement(&mut self, stat: StatId) -> DirectId {
        checkpoint();
        match self.ir[stat].kind {
            StatementKind::BasicBlock { .. } => self.flatten_basic_block(stat),
            StatementKind::Catch { resources, .. } => self.flatten_try(stat, false, resources),
            StatementKind::CatchAll { is_finally, .. } => self.flatten_try(stat, is_finally, None),
            StatementKind::Do(loop_stat) => self.flatten_loop(stat, loop_stat),
            StatementKind::Synchronized { head_exprents, .. } => {
                self.flatten_synchronized(stat, head_exprents)
            }
            StatementKind::Switch(ref switch) => self.flatten_switch(stat, switch.head_exprents),
            StatementKind::If(branches) => self.flatten_if(stat, branches),
            StatementKind::Sequence | StatementKind::Root { .. } => self.flatten_sequence(stat),
            StatementKind::General { .. } | StatementKind::DummyExit { .. } => {
                panic!(
                    "Unexpected statement {} in the direct graph",
                    self.ir[stat].id
                );
            }
        }
    }

    fn flatten_basic_block(&mut self, stat: StatId) -> DirectId {
        let node = self.create_node(stat, NodeType::Direct, self.ir[stat].exprents);
        self.regular_destinations.insert(stat, node);
        let successors = stat.get_successor_edges(self.ir, STATEDGE_DIRECT_ALL);
        if self.ir[stat].last_basic_type == LastBasicType::If {
            let edge = *successors
                .first()
                .expect("Empty successor list for conditional node");
            self.positive_if_branches
                .insert(node, self.ir[edge].destination);
        }
        self.handle_sequence_predecessor(stat);
        self.defer_edges(node, &successors);
        node
    }

    fn flatten_try(
        &mut self,
        stat: StatId,
        is_finally: bool,
        resources: Option<ExprListId>,
    ) -> DirectId {
        let node = self.create_node(stat, NodeType::Try, self.nonempty_list(resources));
        self.regular_destinations.insert(stat, node);

        let end_catch_index = self.ir[stat].stats.len() - usize::from(is_finally);
        if is_finally {
            let finally = self.create_node(stat, NodeType::Finally, None);
            self.finally_nodes.push(finally);
        }

        self.try_nodes.push(Vec::new());
        let try_block = self.flatten_statement(self.ir[stat].first.unwrap());
        self.graph.connect(node, try_block, DirectEdgeType::Regular);
        let inner_try_nodes = self.try_nodes.pop().unwrap();
        if let Some(outer_try_nodes) = self.try_nodes.last_mut() {
            outer_try_nodes.extend(inner_try_nodes.iter().copied());
        }

        let combined_catch = self.create_node(stat, NodeType::CombinedCatch, None);
        for inner in inner_try_nodes {
            self.graph
                .connect(inner, combined_catch, DirectEdgeType::Exception);
        }
        self.graph
            .connect(node, combined_catch, DirectEdgeType::Regular);

        for index in 1..end_catch_index {
            let handler = self.ir[stat].stats[index];
            let catch_node = self.create_node(handler, NodeType::Catch, None);
            let handler_node = self.flatten_statement(handler);
            self.graph
                .connect(combined_catch, catch_node, DirectEdgeType::Regular);
            self.graph
                .connect(catch_node, handler_node, DirectEdgeType::Regular);
        }

        if is_finally {
            let finally = self.finally_nodes.pop().unwrap();
            debug_assert_eq!(self.graph[finally].ty, NodeType::Finally);
            debug_assert_eq!(self.graph[finally].stat, stat);
            self.graph
                .connect(combined_catch, finally, DirectEdgeType::Regular);

            let finally_end = self.create_node(stat, NodeType::FinallyEnd, None);
            self.finally_nodes.push(finally_end);
            let body = self.flatten_statement(self.ir[stat].stats[end_catch_index]);
            self.graph.connect(finally, body, DirectEdgeType::Regular);
            self.finally_nodes.pop();
        }
        node
    }

    fn flatten_loop(&mut self, stat: StatId, loop_stat: DoStatement) -> DirectId {
        if loop_stat.ty == LoopType::Infinite {
            self.link_infinite_loop_predecessor(stat);
        }

        let body = self.flatten_statement(self.ir[stat].first.unwrap());
        let (entry, continue_to, exit_from) = match loop_stat.ty {
            LoopType::Infinite => {
                self.regular_destinations.insert(stat, body);
                self.continue_destinations.insert(stat, body);
                return body;
            }
            LoopType::While | LoopType::DoWhile => {
                let condition = self.create_node(stat, NodeType::Condition, loop_stat.condition);
                self.graph.connect(condition, body, DirectEdgeType::Regular);
                let entry = if loop_stat.ty == LoopType::While {
                    condition
                } else {
                    body
                };
                (entry, condition, condition)
            }
            LoopType::For => {
                let init = self.create_node(stat, NodeType::Init, self.nonempty_list(loop_stat.init));
                let condition = self.create_node(stat, NodeType::Condition, loop_stat.condition);
                let increment = self.create_node(stat, NodeType::Increment, loop_stat.increment);
                self.graph.connect(condition, body, DirectEdgeType::Regular);
                self.graph.connect(init, condition, DirectEdgeType::Regular);
                self.graph.connect(increment, condition, DirectEdgeType::Regular);
                (init, increment, condition)
            }
            LoopType::ForEach => {
                let iterable = self.create_node(stat, NodeType::Increment, loop_stat.increment);
                let variable = self.create_node(stat, NodeType::ForeachVardef, loop_stat.init);
                self.graph.connect(variable, body, DirectEdgeType::Regular);
                self.graph.connect(iterable, variable, DirectEdgeType::Regular);
                (iterable, variable, variable)
            }
        };

        self.regular_destinations.insert(stat, entry);
        self.continue_destinations.insert(stat, continue_to);
        if loop_stat.ty != LoopType::While {
            self.handle_loop_end(stat, body);
        }
        let successor = self.ir[stat]
            .first_successor()
            .expect("Enhanced loop has no successor");
        self.defer_edge(exit_from, successor);
        entry
    }

    fn link_infinite_loop_predecessor(&mut self, stat: StatId) {
        let regular = EdgeType::Regular.mask();
        if let Some(&edge) = stat.get_successor_edges(self.ir, regular).first() {
            let target = self.ir[edge].destination;
            if target.get_predecessor_edges(self.ir, STATEDGE_ALL).len() == 1
                && let Some(&predecessor) = stat.get_predecessor_edges(self.ir, regular).first()
            {
                self.add_edge_if_possible(self.ir[predecessor].source, target);
            }
        }
    }

    fn handle_loop_end(&mut self, stat: StatId, body: DirectId) {
        if !self
            .deferred_edges
            .iter()
            .any(|edge| edge.destination == stat && edge.kind == EdgeType::Continue)
        {
            self.deferred_edges.push(DeferredEdge {
                source: body,
                destination: stat,
                kind: EdgeType::Continue,
            });
        }
    }

    fn flatten_synchronized(
        &mut self,
        stat: StatId,
        head_exprents: Option<ExprListId>,
    ) -> DirectId {
        let (first, out) = self.flatten_head(stat, head_exprents);
        let head = self.ir[stat].first.unwrap();
        self.defer_edges(out, &head.get_successor_edges(self.ir, STATEDGE_DIRECT_ALL));
        self.flatten_statement(self.ir[stat].stats[1]);
        self.handle_sequence_predecessor(stat);
        first
    }

    fn flatten_switch(&mut self, stat: StatId, head_exprents: Option<ExprListId>) -> DirectId {
        let (first, out) = self.flatten_head(stat, head_exprents);
        self.handle_sequence_predecessor(stat);
        self.flatten_remaining_children(stat);

        let StatementKind::Switch(switch) = &self.ir[stat].kind else {
            unreachable!();
        };
        let case_count = switch.cases.len();
        let default_edge = {
            let mut trailing_values = switch.case_values().skip(case_count);
            trailing_values.next().map(|values| {
                assert!(
                    values == [None] && trailing_values.next().is_none(),
                    "Case edges and case values do not match"
                );
                switch.default_edge
            })
        };
        for index in 0..case_count {
            let StatementKind::Switch(switch) = &self.ir[stat].kind else {
                unreachable!();
            };
            let case = &switch.cases[index];
            let statement = case.statement;
            let edges = case.edges.clone();
            let values = case.values.iter().flatten().copied().collect();
            let expressions = self.ir.new_list(values);
            let case_node = self.create_node(statement, NodeType::Case, Some(expressions));
            self.graph.connect(out, case_node, DirectEdgeType::Regular);
            self.defer_edges(case_node, &edges);
        }
        if let Some(edge) = default_edge {
            self.defer_edge(out, edge.expect("Missing switch default edge"));
        }
        first
    }

    fn flatten_if(&mut self, stat: StatId, branches: IfStatement) -> DirectId {
        let (first, out) = self.flatten_head(stat, branches.head_exprents);
        let if_edge = branches
            .if_edge
            .expect("Conditional statement has no if edge");
        self.positive_if_branches
            .insert(out, self.ir[if_edge].destination);
        self.handle_sequence_predecessor(stat);
        self.flatten_remaining_children(stat);

        let head = self.ir[stat].first.unwrap();
        self.defer_edges(out, &head.get_successor_edges(self.ir, STATEDGE_DIRECT_ALL));
        if !branches.has_else
            && let Some(&successor) = stat
                .get_successor_edges(self.ir, STATEDGE_DIRECT_ALL)
                .first()
        {
            self.defer_edge(out, successor);
        }
        first
    }

    fn flatten_head(
        &mut self,
        stat: StatId,
        head_exprents: Option<ExprListId>,
    ) -> (DirectId, DirectId) {
        let head = self.ir[stat].first.unwrap();
        let first = self.create_node(head, NodeType::Direct, self.ir[head].exprents);
        self.regular_destinations.insert(head, first);
        self.regular_destinations.insert(stat, first);
        let mut out = first;
        if let Some(exprents) = self.nonempty_list(head_exprents) {
            out = self.create_node(stat, NodeType::Tail, Some(exprents));
            self.graph.connect(first, out, DirectEdgeType::Regular);
        }
        (first, out)
    }

    fn flatten_sequence(&mut self, stat: StatId) -> DirectId {
        let first = self.flatten_statement(self.ir[stat].first.unwrap());
        self.flatten_remaining_children(stat);
        self.regular_destinations.insert(stat, first);
        first
    }

    fn flatten_remaining_children(&mut self, stat: StatId) {
        for index in 1..self.ir[stat].stats.len() {
            self.flatten_statement(self.ir[stat].stats[index]);
        }
    }

    fn nonempty_list(&self, exprents: Option<ExprListId>) -> Option<ExprListId> {
        exprents.filter(|&exprents| !self.ir[exprents].is_empty())
    }

    fn handle_sequence_predecessor(&mut self, stat: StatId) {
        if let [predecessor] = stat.get_predecessor_edges(self.ir, STATEDGE_ALL).as_slice() {
            let edge = &self.ir[*predecessor];
            let source = edge.source;
            if edge.edge_type == EdgeType::Regular
                && matches!(self.ir[source].kind, StatementKind::Sequence)
            {
                self.add_edge_if_possible(source.get_basic_head(self.ir), stat);
            }
        }
    }

    fn add_edge_if_possible(&mut self, source: StatId, destination: StatId) {
        if let Some(&source) = self.regular_destinations.get(&source) {
            self.deferred_edges.push(DeferredEdge {
                source,
                destination,
                kind: EdgeType::Regular,
            });
        }
    }

    fn defer_edges(&mut self, source: DirectId, edges: &[EdgeId]) {
        for &edge in edges {
            self.defer_edge(source, edge);
        }
    }

    fn defer_edge(&mut self, source: DirectId, edge: EdgeId) {
        let edge = &self.ir[edge];
        self.deferred_edges.push(DeferredEdge {
            source,
            destination: edge.destination,
            kind: edge.edge_type,
        });
    }

    fn resolve_edges(&mut self) {
        for edge in &self.deferred_edges {
            let destinations = if edge.kind == EdgeType::Continue {
                &self.continue_destinations
            } else {
                &self.regular_destinations
            };
            let mut destination = *destinations.get(&edge.destination).unwrap_or_else(|| {
                let source = self.graph[edge.source].stat;
                panic!(
                    "Could not find destination nodes for statement {} from statement {}",
                    self.ir[edge.destination].id, self.ir[source].id
                );
            });

            if edge.kind == EdgeType::FinallyExit {
                let Some(finally) = self.graph[edge.source]
                    .try_finally
                    .filter(|&scope| self.graph[scope].ty == NodeType::FinallyEnd)
                else {
                    // An unprocessed finally can still leave a finally-exit edge.
                    continue;
                };
                destination = finally;
            }

            let kind = if edge.kind == EdgeType::Exception {
                DirectEdgeType::Exception
            } else {
                DirectEdgeType::Regular
            };
            self.graph.connect(edge.source, destination, kind);
            if let Some(&positive) = self.positive_if_branches.get(&edge.source)
                && edge.destination != positive
            {
                self.graph.neg_if_branch.insert(edge.source, destination);
            }
        }
    }
}
