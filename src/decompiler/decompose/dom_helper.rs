// Copyright 2000-2020 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! The initial statement graph built by `decompose.DomHelper`.

use std::sync::Arc;

use crate::code::cfg::ControlFlowGraph;
use crate::decompiler::ir::{Ir, StatId};
use crate::decompiler::stats::Statement;
use crate::decompiler::stats::stat_edge::{EdgeType, StatEdge};
use crate::engine::counter_container::CounterContainer;
use crate::structs::StructMethod;
use crate::util::vb_style_collection::VBStyleCollection;

pub fn graph_to_statement(
    ir: &mut Ir,
    counters: &mut CounterContainer,
    graph: &ControlFlowGraph,
    method: Arc<StructMethod>,
) -> StatId {
    let mut stats = VBStyleCollection::with_capacity(graph.blocks.len());
    for &block in graph.blocks.iter() {
        let stat = Statement::new_basic_block(ir, counters, block);
        stats.add_with_key(stat, ir[block].id);
    }

    let first = *stats.get_with_key(&ir[graph.first].id).unwrap();
    let dummy_exit = Statement::new_dummy_exit(ir, counters);
    if stats.len() == 1 && !graph.first.is_successor(ir, graph.first) {
        let root = Statement::new_root(ir, counters, first, dummy_exit, method);
        let edge = StatEdge::new(ir, EdgeType::Break, first, dummy_exit, Some(root));
        first.add_successor(ir, edge);
        return root;
    }

    let general = Statement::new_general(ir, counters, first, stats.iter().copied(), None);
    for &block in graph.blocks.iter() {
        let stat = *stats.get_with_key(&ir[block].id).unwrap();

        for index in 0..ir[block].succs.len() {
            let successor = ir[block].succs[index];
            let successor_id = ir[successor].id;
            let successor_stat = stats.get_with_key(&successor_id).copied();
            let (edge_type, destination) = if successor_stat == Some(first) {
                (EdgeType::Continue, general)
            } else if graph.finally_exits.contains(&block) {
                (EdgeType::FinallyExit, dummy_exit)
            } else if successor_id == ir[graph.last].id {
                (EdgeType::Break, dummy_exit)
            } else {
                (
                    EdgeType::Regular,
                    successor_stat.expect("Successor has no statement"),
                )
            };

            let closure = (edge_type != EdgeType::Regular).then_some(general);
            let edge = StatEdge::new(ir, edge_type, stat, destination, closure);
            stat.add_successor(ir, edge);
        }

        for index in 0..ir[block].succ_exceptions.len() {
            let handler = ir[block].succ_exceptions[index];
            let range = graph
                .get_exception_range(handler, block)
                .expect("Exception edge has no range");
            if !range.is_circular() {
                let handler_stat = *stats.get_with_key(&ir[handler].id).unwrap();
                let edge =
                    StatEdge::new_exception(ir, stat, handler_stat, range.exception_types.clone());
                stat.add_successor(ir, edge);
            }
        }
    }

    general.build_continue_set(ir);
    general.build_monitor_flags(ir);
    Statement::new_root(ir, counters, general, dummy_exit, method)
}
