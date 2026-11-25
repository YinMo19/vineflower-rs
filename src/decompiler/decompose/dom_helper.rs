// Copyright 2000-2020 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! The initial statement graph built by `decompose.DomHelper`.

use std::sync::Arc;

use super::{
    irreducible,
    regions::{self, ExtendedPosts},
    statement_order,
};
use crate::code::cfg::ControlFlowGraph;
use crate::decompiler::ir::{Ir, StatId};
use crate::decompiler::stats::stat_edge::{EdgeType, StatEdge};
use crate::decompiler::stats::{Statement, StatementKind, recognize::detect_statement};
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

/// The reduction step in DomHelper.parseGraph, before label and sequence cleanup.
pub fn process_statement(
    ir: &mut Ir,
    counters: &mut CounterContainer,
    root: StatId,
    try_loop_fix: bool,
) -> bool {
    let child = ir[root].first.expect("root has no head");
    if matches!(ir[child].kind, StatementKind::BasicBlock { .. }) {
        return true;
    }
    let mut initial = ExtendedPosts::Linked(Default::default());
    if !reduce_general(ir, counters, child, root, &mut initial, try_loop_fix) {
        return false;
    }
    root.replace_statement(ir, child, ir[child].first.unwrap());
    true
}

fn reduce_general(
    ir: &mut Ir,
    counters: &mut CounterContainer,
    general: StatId,
    root: StatId,
    inherited: &mut ExtendedPosts,
    try_loop_fix: bool,
) -> bool {
    let mut refreshed = inherited.is_empty();
    // Replacing the Java local map changes which mutations reach the caller.
    // A nested reduction initially uses the caller's map only for its head.
    let mut local;
    let mut posts = &mut *inherited;
    for map_stage in 0..2 {
        let mut attempt = 0;
        while attempt < 5 {
            if attempt > 0 {
                if !irreducible::is_irreducible(ir, general)
                    || !irreducible::split(ir, counters, general)
                {
                    break;
                }
                if attempt == 4 && (map_stage == 1 || refreshed) {
                    add_root_comment(
                        ir,
                        root,
                        "$VF: Irreducible bytecode has more than 5 nodes in sequence and was not entirely decomposed",
                        true,
                    );
                }
                add_root_comment(
                    ir,
                    root,
                    "$VF: Irreducible bytecode was duplicated to produce valid code",
                    false,
                );
                local = ExtendedPosts::fresh();
                posts = &mut local;
                refreshed = true;
            }
            for force_all in [false, true] {
                loop {
                    if find_simple(ir, counters, general, posts, try_loop_fix) {
                        attempt = 0;
                    }
                    if general.is_placeholder(ir) {
                        return true;
                    }
                    let Some(region) =
                        regions::find_general(ir, counters, general, force_all, posts)
                    else {
                        break;
                    };
                    let nested_posts = if ir[general].first == Some(region) {
                        &mut *posts
                    } else {
                        &mut ExtendedPosts::fresh()
                    };
                    if !reduce_general(ir, counters, region, root, nested_posts, try_loop_fix) {
                        return false;
                    }
                    general.replace_statement(ir, region, ir[region].first.unwrap());
                    local = ExtendedPosts::fresh();
                    posts = &mut local;
                    refreshed = true;
                    attempt = 0;
                }
            }
            attempt += 1;
        }
        if refreshed {
            break;
        }
        local = ExtendedPosts::fresh();
        posts = &mut local;
    }
    false
}

fn find_simple(
    ir: &mut Ir,
    counters: &mut CounterContainer,
    general: StatId,
    posts: &mut ExtendedPosts,
    try_loop_fix: bool,
) -> bool {
    let mut changed = false;
    loop {
        let candidate = statement_order::post_reverse_post_order(ir, general)
            .into_iter()
            .find_map(|head| detect_statement(ir, counters, head, try_loop_fix));
        let Some(result) = candidate else {
            return changed;
        };
        if !general.is_placeholder(ir)
            && ir[result].first == ir[general].first
            && ir[result].stats.len() == ir[general].stats.len()
        {
            general.set_placeholder(ir);
        }
        general.collapse_nodes_to_statement(ir, counters, result);
        posts.collapse(ir, result);
        changed = true;
    }
}

fn add_root_comment(ir: &mut Ir, root: StatId, text: &str, error: bool) {
    let StatementKind::Root {
        comment_lines,
        add_error_comment,
        ..
    } = &mut ir[root].kind
    else {
        unreachable!()
    };
    comment_lines
        .get_or_insert_with(Default::default)
        .insert(text.to_owned());
    *add_error_comment |= error;
}
