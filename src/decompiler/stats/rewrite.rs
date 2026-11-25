// Copyright 2000-2024 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Tree and edge changes shared by statement recognition and replacement.

use rustc_hash::FxHashSet;

use super::recognize;
use super::stat_edge::{EdgeType, StatEdge};
use super::{EdgeDirection, STATEDGE_ALL, STATEDGE_DIRECT_ALL};
use crate::decompiler::ir::{Ir, StatId};
use crate::engine::counter_container::CounterContainer;

impl StatId {
    /// Looks through the child tree even while a candidate's parent links
    /// still point into its enclosing general statement.
    pub fn contains_statement_strict(self, ir: &Ir, target: StatId) -> bool {
        let mut pending = vec![self];
        while let Some(parent) = pending.pop() {
            let children = &ir[parent].stats;
            if children.contains(&target) {
                return true;
            }
            pending.extend(
                children
                    .iter()
                    .copied()
                    .filter(|&child| !ir[child].stats.is_empty()),
            );
        }
        false
    }

    pub fn collapse_nodes_to_statement(
        self,
        ir: &mut Ir,
        counters: &mut CounterContainer,
        stat: StatId,
    ) {
        let head = ir[stat].first.expect("a region needs a head");
        let post = ir[stat].post;
        if let Some(post) = post {
            for edge in post.get_predecessor_edges(ir, STATEDGE_DIRECT_ALL) {
                if stat.contains_statement_strict(ir, ir[edge].source) {
                    edge.change_type(ir, EdgeType::Break);
                    stat.add_labeled_edge(ir, edge);
                }
            }
        }
        for edge in head.get_predecessor_edges(ir, STATEDGE_ALL) {
            if ir[edge].edge_type != EdgeType::Exception
                && stat.contains_statement_strict(ir, ir[edge].source)
            {
                edge.change_type(ir, EdgeType::Continue);
                stat.add_labeled_edge(ir, edge);
            }
            edge.change_destination(ir, stat);
        }
        if ir[stat].stats.contains_key(&ir[ir[self].first.unwrap()].id) {
            ir[self].first = Some(stat);
        }

        let children = ir[stat].stats.to_vec();
        let mask = EdgeType::Exception.mask();
        let mut handlers: FxHashSet<_> = head
            .get_neighbours(ir, mask, EdgeDirection::Forward)
            .into_iter()
            .collect();
        for &child in &children {
            if handlers.is_empty() {
                break;
            }
            let child_handlers = child.get_neighbours(ir, mask, EdgeDirection::Forward);
            handlers.retain(|handler| child_handlers.contains(handler));
        }
        if !handlers.is_empty() {
            for edge in head.get_successor_edges(ir, mask) {
                let handler = ir[edge].destination;
                if handlers.contains(&handler) && !ir[stat].stats.contains_key(&ir[handler].id) {
                    let edge =
                        StatEdge::new_exception(ir, stat, handler, ir[edge].exceptions.clone());
                    stat.add_successor(ir, edge);
                }
            }
            for &child in &children {
                for edge in child.get_successor_edges(ir, mask) {
                    if handlers.contains(&ir[edge].destination) {
                        edge.remove(ir);
                    }
                }
            }
        }
        if let Some(post) = post
            && !stat
                .get_neighbours(ir, mask, EdgeDirection::Forward)
                .contains(&post)
        {
            let edge = StatEdge::new(ir, EdgeType::Regular, stat, post, None);
            stat.add_successor(ir, edge);
        }
        for child in children {
            let key = ir[child].id;
            ir[self].stats.remove_with_key(&key);
        }
        let key = ir[stat].id;
        ir[self].stats.add_with_key(stat, key);
        stat.set_all_parent(ir);
        ir[stat].parent = Some(self);
        stat.build_continue_set(ir);
        stat.build_monitor_flags(ir);
        recognize::on_node_collapse(ir, counters, stat);
    }

    pub fn replace_statement(self, ir: &mut Ir, old: StatId, new: StatId) {
        let index = ir[self].stats.get_index_by_key(&ir[old].id);
        for edge in old.get_predecessor_edges(ir, STATEDGE_ALL) {
            edge.change_destination(ir, new);
        }
        // remove/add also moves this edge to the end of the destination's
        // predecessor lists, which change_source alone would not do.
        for edge in old.get_successor_edges(ir, STATEDGE_ALL) {
            edge.remove(ir);
            ir[edge].source = new;
            new.add_successor(ir, edge);
        }
        let (old_id, new_id) = (ir[old].id, ir[new].id);
        ir[self].stats.remove_with_key(&old_id);
        ir[self].stats.add_with_key_and_index(index, new, new_id);
        ir[new].parent = Some(self);
        ir[new].post = ir[old].post;
        if ir[self].first == Some(old) {
            ir[self].first = Some(new);
        }
        let labels = ir[old]
            .label_edges
            .iter()
            .copied()
            .rev()
            .collect::<Vec<_>>();
        for edge in labels {
            if ir[edge].source != new {
                new.add_labeled_edge(ir, edge);
            } else if ir[edge].destination == self
                || self.contains_statement_strict(ir, ir[edge].destination)
            {
                ir[edge].closure = None;
            } else {
                self.add_labeled_edge(ir, edge);
            }
        }
        let mut pending = vec![self];
        while let Some(node) = pending.pop() {
            for edge in node.get_successor_edges(ir, STATEDGE_ALL) {
                if ir[edge].closure == Some(old) {
                    ir[edge].closure = Some(new);
                }
            }
            pending.extend(ir[node].stats.iter().rev().copied());
        }
        ir[old].label_edges.clear();
        recognize::replace_child(ir, self, old, new);
    }
}
