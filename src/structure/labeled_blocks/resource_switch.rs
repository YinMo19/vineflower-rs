use std::collections::BTreeSet;

use super::{Edges, Emitter, Plan, Region};
use crate::structure::exception_emit::ExceptionRedirect;

impl Emitter<'_> {
    /// A verified resource normal-close projection replaces several raw
    /// cleanup entries with one lexical continuation. Only entries owned by
    /// this resource arm may participate in its synthesized labeled scope.
    pub(super) fn labeled_resource_switch(&self, head: usize, region: Region<'_, '_, '_>) -> Option<Plan> {
        let (arm, join) = (region.exception_arm?, region.stop?);
        if region.label_scope().is_some() || region.loop_header.is_some() || region.protected.is_none() {
            return None;
        }
        let projects = |block: usize| {
            matches!(self.exception_redirects.get(&block), Some(ExceptionRedirect::Continue { target, arm: owner })
                if *target == join && *owner == arm)
        };
        let returns = |block: usize| {
            matches!(self.exception_redirects.get(&block), Some(ExceptionRedirect::ReturnAtEdge { arm: owner, .. })
                if *owner == arm)
        };
        if self.exception_redirects.keys().copied().filter(|&block| projects(block)).take(2).count() < 2 {
            return None;
        }
        let cfg = &self.graph.blocks;
        let targets = &cfg[head].successors;
        if targets.len() < 2 || targets.iter().any(|&target| target <= head || projects(target) || returns(target)) {
            return None;
        }
        // The tail is reached by ordinary switch breaks or default
        // fallthrough, not by another direct switch dispatch.
        let tail = self.layout.common_join(self.graph, region, targets.iter().map(|&target| (target, None)))?;
        if tail <= head || tail >= join || targets.iter().any(|&target| target >= tail) {
            return None;
        }
        let [normal_cleanup] = *cfg[tail].successors.as_slice() else { return None; };
        if !projects(normal_cleanup) { return None; }
        let mut visited = BTreeSet::new();
        let mut abrupt_entries = BTreeSet::new();
        let mut return_entries = BTreeSet::new();
        let mut break_count = 0;
        let mut pending = vec![head];
        while let Some(block) = pending.pop() {
            if !visited.insert(block) { continue; }
            let node = &cfg[block];
            let owned_body = match self.exception_redirects.get(&block) {
                Some(ExceptionRedirect::ReturnSpill { store, arm: owner }) if *owner == arm => {
                    node.instructions.end == store + 1 && node.instructions.contains(store)
                        && matches!(node.successors.as_slice(), [next] if returns(*next))
                        && self.exceptions.contains(Some(arm), block)
                        && self.exceptions.at_start(Some(arm), block).is_none()
                        && self.exceptions.bypass_cleanup(block) == block
                        && self.layout.loops[block].is_none()
                        && node.exception_predecessors.is_empty()
                        && node.instructions.clone().all(|index| {
                            !self.exceptions.skips_instruction(index)
                                && !matches!(self.instructions[index].opcode, 0xc2 | 0xc3)
                        })
                }
                _ => self.labeled_region_block(block, region),
            };
            if block > tail || !self.layout.inside(block, region)
                || !owned_body
                || (block != head && self.emitted[block])
                || node.exception_successors != cfg[head].exception_successors
                || !self.exceptions.matches_dispatch(block, head, None)
                || node.successors.is_empty()
                || (block != head && matches!(self.instructions[node.instructions.end - 1].opcode, 0xaa | 0xab))
            {
                return None;
            }
            for &next in &node.successors {
                if next <= block { return None; }
                if projects(next) {
                    // Only a real sole outgoing edge from a proved block
                    // can carry a projected close, never a conditional edge.
                    if node.successors.len() != 1 || !cfg[next].exception_predecessors.is_empty()
                        || (block != tail && next == normal_cleanup)
                    {
                        return None;
                    }
                    if block != tail {
                        abrupt_entries.insert(next);
                        break_count += 1;
                    }
                } else if returns(next) {
                    // The scoped redirect will emit the proven return when
                    // this path advances to its raw close entry. It neither
                    // reaches the label join nor needs a synthetic break.
                    if node.successors.len() != 1 || !cfg[next].exception_predecessors.is_empty() {
                        return None;
                    }
                    return_entries.insert(next);
                } else {
                    if next > tail { return None; }
                    pending.push(next);
                }
            }
        }
        if !visited.contains(&tail) || break_count == 0 {
            return None;
        }
        // Both the lexical body and every reached cleanup projection must
        // be exclusively owned by this source switch region. The original
        // protected arm records which blocks may execute the implicit close.
        if visited.iter().copied().filter(|&block| block != head)
            .chain(abrupt_entries.iter().copied()).chain([normal_cleanup]).chain(return_entries)
            .any(|block| cfg[block].predecessors.is_empty()
                || cfg[block].predecessors.iter().any(|pred| !visited.contains(pred)))
        {
            return None;
        }
        Some(Plan { tail, join, break_count, edges: Edges::Resource { arm, abrupt_entries } })
    }
}
