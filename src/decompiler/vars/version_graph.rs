// Copyright 2000-2018 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! `VarVersionsGraph` and `VarVersionNode`: SSAU's value-use dependencies.

use std::collections::VecDeque;
use std::ops::{Index, IndexMut};
use std::sync::Arc;

use indexmap::IndexSet;
use rustc_hash::FxHashSet;

use super::var_version_pair::VarVersionPair;
use crate::decompiler::decompose::generic_dominator_engine::GenericDominatorEngine;
use crate::decompiler::sforms::VersionMap;
use crate::structs::attr::LocalVariable;
use crate::util::vb_style_collection::VBStyleCollection;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VersionState {
    Write,
    Read,
    Phi,
    DeadRead,
    Phantom,
    Param,
    Catch,
}

#[derive(Debug)]
pub struct VarVersionNode {
    pub var: i32,
    pub version: i32,
    pub successors: IndexSet<VarVersionPair>,
    pub predecessors: IndexSet<VarVersionPair>,
    pub phantom_node: Option<VarVersionPair>,
    pub phantom_parent_node: Option<VarVersionPair>,
    pub live: Option<VersionMap>,
    pub lvt: Option<Arc<LocalVariable>>,
    pub state: Option<VersionState>,
}

impl VarVersionNode {
    pub fn as_pair(&self) -> VarVersionPair {
        VarVersionPair::new(self.var, self.version)
    }

    pub fn single_predecessor(&self) -> VarVersionPair {
        *self
            .predecessors
            .first()
            .expect("version has no predecessor")
    }
}

#[derive(Default)]
pub struct VarVersionsGraph {
    /// Versions in allocation order. The pairs also identify graph edges.
    pub nodes: VBStyleCollection<VarVersionNode, VarVersionPair>,
    dominators: Option<GenericDominatorEngine<VarVersionPair>>,
}

impl VarVersionsGraph {
    pub fn create_node(
        &mut self,
        pair: VarVersionPair,
        lvt: Option<Arc<LocalVariable>>,
        state: Option<VersionState>,
    ) {
        self.nodes.add_with_key(
            VarVersionNode {
                var: pair.var,
                version: pair.version,
                successors: IndexSet::new(),
                predecessors: IndexSet::new(),
                phantom_node: None,
                phantom_parent_node: None,
                live: None,
                lvt,
                state,
            },
            pair,
        );
    }

    pub fn get(&self, pair: VarVersionPair) -> Option<&VarVersionNode> {
        self.nodes.get_with_key(&pair)
    }

    pub fn add_read_edge(&mut self, source: VarVersionPair, destination: VarVersionPair) {
        self[source].successors.insert(destination);
        self[destination].predecessors.insert(source);
    }

    pub fn remove_read_edge(&mut self, source: VarVersionPair, destination: VarVersionPair) {
        self[source].successors.shift_remove(&destination);
        self[destination].predecessors.shift_remove(&source);
    }

    pub fn init_dominators(&mut self) {
        let roots: Vec<_> = self
            .nodes
            .iter()
            .filter(|node| node.predecessors.is_empty())
            .map(VarVersionNode::as_pair)
            .collect();
        self.dominators = Some(GenericDominatorEngine::new(
            &self.reverse_post_order(&roots),
            |pair| self[pair].predecessors.is_empty(),
            |pair| self[pair].predecessors.iter().copied(),
        ));
    }

    pub fn is_dominator_set(
        &self,
        node: VarVersionPair,
        dominators: &FxHashSet<VarVersionPair>,
    ) -> bool {
        if dominators.len() == 1 {
            let dom = *dominators.iter().next().unwrap();
            return self
                .dominators
                .as_ref()
                .expect("version dominators have not been initialized")
                .is_dominator(node, dom);
        }
        if dominators.contains(&node) {
            return true;
        }

        let mut seen = FxHashSet::default();
        let mut queue = VecDeque::from([node]);
        while let Some(pair) = queue.pop_front() {
            if !seen.insert(pair) {
                continue;
            }
            let predecessors = &self[pair].predecessors;
            if predecessors.is_empty() {
                return false;
            }
            queue.extend(
                predecessors
                    .iter()
                    .copied()
                    .filter(|pred| !dominators.contains(pred)),
            );
        }
        true
    }

    pub fn are_vars_analogous(&self, var_base: i32, var_check: i32) -> bool {
        let mut seen = FxHashSet::default();
        let mut queue = VecDeque::from([VarVersionPair::new(var_base, 1)]);
        while let Some(pair) = queue.pop_front() {
            if !seen.insert(pair) {
                continue;
            }
            let node = &self[pair];
            let Some(analog) = self.get(VarVersionPair::new(var_check, pair.version)) else {
                return false;
            };
            if node.successors.len() != analog.successors.len() {
                return false;
            }
            for &destination in &node.successors {
                if self
                    .get(VarVersionPair::new(var_check, destination.version))
                    .is_none()
                {
                    return false;
                }
                queue.push_back(destination);
            }
        }
        true
    }

    fn reverse_post_order(&self, roots: &[VarVersionPair]) -> Vec<VarVersionPair> {
        let mut result = Vec::with_capacity(self.nodes.len());
        let mut seen = FxHashSet::default();
        let mut stack = Vec::new();
        for &root in roots {
            let start = result.len();
            seen.insert(root);
            stack.push((root, self[root].successors.iter()));
            while let Some((pair, successors)) = stack.last_mut() {
                if let Some(&child) = successors.next() {
                    if seen.insert(child) {
                        stack.push((child, self[child].successors.iter()));
                    }
                } else {
                    result.push(*pair);
                    stack.pop();
                }
            }

            result[start..].reverse();
        }
        result
    }
}

impl Index<VarVersionPair> for VarVersionsGraph {
    type Output = VarVersionNode;

    fn index(&self, pair: VarVersionPair) -> &VarVersionNode {
        self.get(pair)
            .unwrap_or_else(|| panic!("missing variable version {pair}"))
    }
}

impl IndexMut<VarVersionPair> for VarVersionsGraph {
    fn index_mut(&mut self, pair: VarVersionPair) -> &mut VarVersionNode {
        self.nodes
            .get_with_key_mut(&pair)
            .unwrap_or_else(|| panic!("missing variable version {pair}"))
    }
}
