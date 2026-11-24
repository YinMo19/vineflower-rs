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

#[cfg(test)]
mod tests {
    use crate::structure::exception_tests::{handler, test_method_with_descriptor};

    #[test]
    fn same_arm_closes_are_projected_without_moving_normal_switch_tail() {
        let bytes = [
            0x2a, 0x4d, 0x1b, 0xab, // 0: acquire alias; 3: lookupswitch
            0, 0, 0, 47, 0, 0, 0, 2, // default -> 50; two keys
            0, 0, 0, 1, 0, 0, 0, 25, // 1 -> 28
            0, 0, 0, 2, 0, 0, 0, 31, // 2 -> 34
            0xb8, 0, 22, 0xa7, 0, 22, // 28: work(); goto 53
            0xb8, 0, 22, // 34: work(); fall through to early close
            0x2c, 0xc6, 0, 55, // 37: early normal close guard -> 93 if null
            0x2c, 0xb9, 0, 13, 1, 0, 0xa7, 0, 46, // 41: close(); goto 93
            0xb8, 0, 22, // 50: work(); default falls through
            0xb8, 0, 22, // 53: work(); shared tail
            0x2c, 0xc6, 0, 36, // 56: late normal close guard
            0x2c, 0xb9, 0, 13, 1, 0, 0xa7, 0, 27, // 60: close(); goto 93
            0x4e, 0x2c, 0xc6, 0, 20, // 69: save exception; ifnull -> 91
            0x2c, 0xb9, 0, 13, 1, 0, 0xa7, 0, 11, // 74: exceptional close
            0x3a, 4, 0x2d, 0x19, 4, 0xb6, 0, 19, // 83: addSuppressed
            0x2d, 0xbf, 0xb1, // 91: rethrow; 93: return
        ];
        let handlers = [handler(2, 37, 69, 15), handler(50, 56, 69, 15), handler(74, 80, 83, 15)];
        let lines = test_method_with_descriptor(&bytes, &handlers, &[], "(Ljava/lang/AutoCloseable;I)V").unwrap();
        assert!(lines.iter().any(|line| line.depth == 1 && line.text == "label93: {"));
        assert!(lines.iter().any(|line| line.depth == 4 && line.text == "break label93;"));
        assert_eq!(lines.iter().filter(|line| line.text == "work();").count(), 4);
        assert!(lines.iter().any(|line| line.depth == 2 && line.text == "work();" && line.offsets.contains(&53)));
        assert!(!lines.iter().any(|line| line.text.contains("close()")));
    }

    #[test]
    fn a_proven_resource_return_is_abrupt_without_becoming_a_label_break() {
        let bytes = [
            0x2a, 0x4d, 0x1b, 0xab, // 0: acquire alias; 3: lookupswitch
            0, 0, 0, 72, 0, 0, 0, 3, // default -> 75; three keys
            0, 0, 0, 1, 0, 0, 0, 33, // 1 -> 36
            0, 0, 0, 2, 0, 0, 0, 39, // 2 -> 42
            0, 0, 0, 3, 0, 0, 0, 55, // 3 -> 58
            0xb8, 0, 22, 0xa7, 0, 39, // 36: work(); goto 78
            0xb8, 0, 22, // 42: work(); then jump past the tail after close
            0x2c, 0xc6, 0, 72, // 45: early close guard -> 118 if null
            0x2c, 0xb9, 0, 13, 1, 0, 0xa7, 0, 63, // 49: close(); goto 118
            0xb8, 0, 22, 0x04, 0x3e, // 58: work(); spill return value 1
            0x2c, 0xc6, 0, 9, // 63: return close guard -> 73 if null
            0x2c, 0xb9, 0, 13, 1, 0, // 67: close()
            0x1d, 0xac, // 73: reload and return 1
            0xb8, 0, 22, // 75: work(); default falls through
            0xb8, 0, 22, // 78: work(); shared tail
            0x2c, 0xc6, 0, 36, // 81: late close guard
            0x2c, 0xb9, 0, 13, 1, 0, 0xa7, 0, 27, // 85: close(); goto 118
            0x4e, 0x2c, 0xc6, 0, 20, // 94: save exception; ifnull -> 116
            0x2c, 0xb9, 0, 13, 1, 0, 0xa7, 0, 11, // 99: exceptional close
            0x3a, 4, 0x2d, 0x19, 4, 0xb6, 0, 19, // 108: addSuppressed
            0x2d, 0xbf, 0x03, 0xac, // 116: rethrow; 118: return 0
        ];
        let handlers = [
            handler(2, 45, 94, 15), handler(58, 63, 94, 15),
            handler(75, 81, 94, 15), handler(99, 105, 108, 15),
        ];
        let lines = test_method_with_descriptor(&bytes, &handlers, &[], "(Ljava/lang/AutoCloseable;I)I").unwrap();
        assert_eq!(lines.iter().filter(|line| line.text == "break label118;").count(), 1);
        assert!(lines.iter().any(|line| line.depth == 4 && line.text == "return 1;"));
        assert!(lines.iter().any(|line| line.depth == 0 && line.text == "return 0;"));
        assert_eq!(lines.iter().filter(|line| line.text == "work();").count(), 5);
    }
}
