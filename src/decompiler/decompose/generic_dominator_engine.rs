// Copyright 2000-2017 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Immediate dominators in reverse postorder, as in `GenericDominatorEngine`.
//! The result is a snapshot: exception-range passes continue to query it
//! while they edit the live graph.

use std::hash::Hash;

use rustc_hash::FxHashMap;

use crate::code::cfg::ControlFlowGraph;
use crate::decompiler::ir::{BlockId, Ir};

pub struct GenericDominatorEngine<N> {
    positions: FxHashMap<N, usize>,
    parents: Vec<usize>,
}

impl<N: Copy + Eq + Hash> GenericDominatorEngine<N> {
    pub fn new<P: IntoIterator<Item = N>>(
        reverse_post_order: &[N],
        is_root: impl Fn(N) -> bool,
        predecessors: impl Fn(N) -> P,
    ) -> Self {
        let positions: FxHashMap<_, _> = reverse_post_order
            .iter()
            .copied()
            .enumerate()
            .map(|(index, node)| (node, index))
            .collect();
        let incoming: Vec<Vec<_>> = reverse_post_order
            .iter()
            .map(|&node| {
                if is_root(node) {
                    return Vec::new();
                }
                predecessors(node)
                    .into_iter()
                    .filter_map(|pred| positions.get(&pred).copied())
                    .collect()
            })
            .collect();
        let mut parents = vec![None; reverse_post_order.len()];
        loop {
            let mut changed = false;
            for (node, preds) in incoming.iter().enumerate() {
                let mut idom = None;
                for &pred in preds.iter().filter(|&&pred| parents[pred].is_some()) {
                    idom = match idom {
                        None => Some(pred),
                        Some(other) => common_parent(other, pred, &parents),
                    };
                    if idom.is_none() {
                        break;
                    }
                }
                let next = idom.or(Some(node));
                changed |= parents[node] != next;
                parents[node] = next;
            }
            if !changed {
                break;
            }
        }
        Self {
            positions,
            parents: parents.into_iter().map(Option::unwrap).collect(),
        }
    }

    /// Immediate dominators indexed by position in the input reverse postorder.
    pub(super) fn immediate_dominator_positions(&self) -> &[usize] {
        &self.parents
    }

    pub fn is_dominator(&self, node: N, dom: N) -> bool {
        if node == dom {
            return true;
        }
        let mut index = self.positions[&node];
        let target = self.positions.get(&dom).copied();
        while Some(index) != target {
            let parent = self.parents[index];
            if parent == index {
                return false;
            }
            index = parent;
        }
        true
    }
}

fn common_parent(mut left: usize, mut right: usize, parents: &[Option<usize>]) -> Option<usize> {
    while left != right {
        let later = if left > right { &mut left } else { &mut right };
        let parent = parents[*later]?;
        if parent == *later {
            return None;
        }
        *later = parent;
    }
    Some(left)
}

impl GenericDominatorEngine<BlockId> {
    pub fn for_cfg(ir: &Ir, graph: &ControlFlowGraph) -> Self {
        Self::new(
            &graph.get_reverse_post_order(ir),
            |node| node == graph.first,
            |node| {
                ir[node]
                    .preds
                    .iter()
                    .chain(&ir[node].pred_exceptions)
                    .copied()
            },
        )
    }
}
