// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use std::collections::VecDeque;

use crate::bytecode::Instruction;
use crate::cfg::ControlFlowGraph;
use crate::lift::Machine;

use super::StructureError;

#[derive(Clone, Copy)]
pub(super) struct Region<'r, 'a, 'c> {
    pub(super) stop: Option<usize>,
    pub(super) loop_header: Option<usize>,
    pub(super) protected: Option<&'r Machine<'a, 'c>>,
    outer: Option<&'r Region<'r, 'a, 'c>>,
}

impl<'r, 'a, 'c> Region<'r, 'a, 'c> {
    pub(super) const METHOD: Self = Self {
        stop: None,
        loop_header: None,
        protected: None,
        outer: None,
    };

    pub(super) fn branch(&'r self, stop: Option<usize>) -> Self {
        Self {
            stop,
            outer: Some(self),
            ..*self
        }
    }

    pub(super) fn loop_body(&'r self, header: usize) -> Self {
        Self {
            stop: Some(header),
            loop_header: Some(header),
            outer: Some(self),
            ..*self
        }
    }

    pub(super) fn try_body(&'r self, stop: Option<usize>, baseline: &'r Machine<'a, 'c>) -> Self {
        Self {
            protected: Some(baseline),
            ..self.branch(stop)
        }
    }

    fn has_stop(&self, block: usize) -> bool {
        let mut next = Some(self);
        while let Some(region) = next {
            if region.stop == Some(block) {
                return true;
            }
            next = region.outer;
        }
        false
    }
}

#[derive(Clone, Copy)]
pub(super) struct While {
    pub(super) body: usize,
    pub(super) exit: usize,
    parent: Option<usize>,
}

pub(super) struct Layout {
    pub(super) loops: Vec<Option<While>>,
    level: Vec<Option<usize>>,
    postdominators: PostDominators,
}

impl Layout {
    pub(super) fn new(
        graph: &ControlFlowGraph,
        instructions: &[Instruction],
    ) -> Result<Self, StructureError> {
        let mut natural_loops = graph.natural_loops();
        natural_loops
            .sort_unstable_by_key(|natural_loop| std::cmp::Reverse(natural_loop.blocks.len()));
        let mut loops = vec![None; graph.blocks.len()];
        let mut level = vec![None; graph.blocks.len()];
        for natural_loop in natural_loops {
            let header = natural_loop.header;
            let unsupported = || StructureError::Flow {
                offset: instructions[graph.blocks[header].instructions.start].offset,
            };
            let inside = |block: usize| natural_loop.blocks.binary_search(&block).is_ok();
            let [first, second] = graph.blocks[header].successors.as_slice() else {
                return Err(unsupported());
            };
            let (body, exit) = match (inside(*first), inside(*second)) {
                (true, false) => (*first, *second),
                (false, true) => (*second, *first),
                _ => return Err(unsupported()),
            };

            // Recognize single-entry, header-tested loops, not arbitrary SCCs.
            // A nested loop header remains a node in its parent's region.
            let parent = level[header];
            for &block in &natural_loop.blocks {
                if level[block] != parent {
                    return Err(unsupported());
                }
                if block != header
                    && graph.blocks[block]
                        .successors
                        .iter()
                        .any(|&next| !inside(next))
                {
                    return Err(unsupported());
                }
                level[block] = Some(header);
            }
            loops[header] = Some(While { body, exit, parent });
        }
        for (header, shape) in loops.iter().enumerate() {
            if let Some(loop_shape) = shape {
                level[header] = loop_shape.parent;
            }
        }
        let postdominators = PostDominators::new(graph.immediate_postdominators());
        Ok(Self {
            loops,
            level,
            postdominators,
        })
    }

    pub(super) fn inside(&self, block: usize, region: Region<'_, '_, '_>) -> bool {
        self.level[block] == region.loop_header && !region.has_stop(block)
    }

    pub(super) fn normal_join(&self, head: usize, region: Region<'_, '_, '_>) -> Option<usize> {
        // Like DomHelper, prefer the nearest common postdominator but never
        // cross a boundary set by the enclosing structured statement.
        let join = self.postdominators.parent[head]?;
        if region.stop == Some(join) {
            return Some(join);
        }
        if !self.inside(join, region)
            || region
                .stop
                .is_some_and(|stop| self.postdominators.contains(join, stop))
        {
            return None;
        }
        Some(join)
    }

    pub(super) fn can_fall_through(&self, from: usize, next: usize, join: Option<usize>) -> bool {
        join != Some(from)
            && !join.is_some_and(|join| self.postdominators.contains(next, join))
            && self.postdominators.contains(next, from)
    }

    pub(super) fn common_join(
        &self,
        graph: &ControlFlowGraph,
        region: Region<'_, '_, '_>,
        arms: impl IntoIterator<Item = (usize, Option<usize>)>,
    ) -> Option<usize> {
        // An early return can hide a normal join from plain postdominance.
        // Propose a shared continuation; emission still verifies that the
        // resulting arm regions are disjoint and finish at that continuation
        // or an explicit terminal statement.
        let mut seen = vec![usize::MAX; graph.blocks.len()];
        let mut queue = VecDeque::new();
        for (start, fallthrough) in arms {
            if !self.inside(start, region) {
                continue;
            }
            queue.push_back(start);
            while let Some(block) = queue.pop_front() {
                if seen[block] == start {
                    continue;
                }
                if seen[block] != usize::MAX {
                    return Some(block);
                }
                seen[block] = start;
                let successors = match &self.loops[block] {
                    Some(loop_shape) => std::slice::from_ref(&loop_shape.exit),
                    None => &graph.blocks[block].successors,
                };
                queue.extend(successors.iter().copied().filter(|&next| {
                    Some(next) != fallthrough && self.inside(next, region) && seen[next] != start
                }));
            }
        }
        None
    }
}

struct PostDominators {
    parent: Vec<Option<usize>>,
    intervals: Vec<(usize, usize)>,
}

impl PostDominators {
    fn new(parent: Vec<Option<usize>>) -> Self {
        // Number the postdominator forest in preorder, beneath a virtual root.
        // A postdominance query then costs one subtree-interval lookup.
        let root = parent.len();
        let mut first_child = vec![None; root + 1];
        let mut next_sibling = vec![None; root];
        for (block, &postdom) in parent.iter().enumerate() {
            next_sibling[block] = first_child[postdom.unwrap_or(root)].replace(block);
        }
        let mut intervals = vec![(0, 0); root];
        let mut next_index = 0;
        let mut dfs = vec![(root, first_child[root])];
        while let Some((node, child)) = dfs.last_mut() {
            if let Some(block) = *child {
                *child = next_sibling[block];
                intervals[block].0 = next_index;
                next_index += 1;
                dfs.push((block, first_child[block]));
            } else {
                if *node != root {
                    intervals[*node].1 = next_index;
                }
                dfs.pop();
            }
        }
        Self { parent, intervals }
    }

    fn contains(&self, parent: usize, node: usize) -> bool {
        let (start, end) = self.intervals[parent];
        (start..end).contains(&self.intervals[node].0)
    }
}
