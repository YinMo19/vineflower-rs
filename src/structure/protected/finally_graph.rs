// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use std::collections::{BTreeMap, BTreeSet};
use std::ops::Range;

use crate::bytecode::{Instruction, Operand};
use crate::cfg::ControlFlowGraph;

use super::{Route, local_touches, normal_exits, reference_load, reference_store};

pub(in crate::structure) struct BranchedFinally {
    pub(in crate::structure) entry: usize,
    pub(in crate::structure) continuation: Option<usize>,
    pub(in crate::structure) removed: BTreeSet<usize>,
    pub(super) blocks: BTreeSet<usize>,
    pub(super) normal_entry: Option<usize>,
    pub(super) tail: usize,
    pub(super) tail_code: Range<usize>,
}

impl BranchedFinally {
    /// Mirrors the exceptional cleanup against its normal copy, mapping
    /// branch destinations rather than comparing byte offsets. The rethrow
    /// of the original exception is the only unmatched handler operation.
    pub(super) fn prove(
        instructions: &[Instruction],
        graph: &ControlFlowGraph,
        routes: &[Vec<Route>],
        body: &BTreeSet<usize>,
        handler: usize,
    ) -> Option<Self> {
        let start = &graph.blocks[handler];
        if handler == 0 || !start.predecessors.is_empty() || body.contains(&handler) {
            return None;
        }
        let slot = reference_store(&instructions[start.instructions.start])?;
        let entry = if start.instructions.len() == 1 {
            let &[next] = start.successors.as_slice() else {
                return None;
            };
            if graph.blocks[next].predecessors != [handler] {
                return None;
            }
            next
        } else {
            handler
        };
        let mut cleanup = BTreeSet::new();
        let mut rethrow = None;
        let mut pending = vec![entry];
        while let Some(index) = pending.pop() {
            if !cleanup.insert(index) {
                continue;
            }
            let block = &graph.blocks[index];
            if body.contains(&index) || (index != handler && !block.exception_predecessors.is_empty())
            {
                return None;
            }
            let start = block.instructions.start + usize::from(index == handler);
            let mut end = block.instructions.end;
            if let [.., load, throw] = &instructions[start..end]
                && reference_load(load) == Some(slot) && throw.opcode == 0xbf
            {
                end -= 2;
                if rethrow.replace((index, start..end)).is_some() {
                    return None;
                }
            }
            if instructions[start..end].iter().any(|op| local_touches(op, slot)) {
                return None;
            }
            pending.extend(block.successors.iter().copied());
        }
        let (tail, tail_code) = rethrow?;
        if entry == tail {
            return None;
        }
        cleanup.insert(handler);
        if cleanup.iter().any(|&block| {
            graph.blocks[block].predecessors.iter().any(|pred| !cleanup.contains(pred))
        }) || body.iter().any(|&block| {
            matches!(instructions[graph.blocks[block].instructions.end - 1].opcode, 0xac..=0xb1)
        }) {
            return None;
        }
        let mut normal_exits: BTreeSet<_> = normal_exits(graph, body).collect();
        if normal_exits.len() > 1 {
            return None;
        }
        let normal_entry = normal_exits.pop_first();
        let mut result = Self {
            entry,
            continuation: None,
            removed: BTreeSet::new(),
            blocks: cleanup,
            normal_entry,
            tail,
            tail_code,
        };
        if let Some(sample) = normal_entry {
            result.match_copy(instructions, graph, routes, body, handler, sample)?;
        }
        Some(result)
    }

    fn match_copy(
        &mut self,
        instructions: &[Instruction],
        graph: &ControlFlowGraph,
        routes: &[Vec<Route>],
        body: &BTreeSet<usize>,
        handler: usize,
        sample_start: usize,
    ) -> Option<()> {
        let mut paired = BTreeMap::new();
        let mut copies = BTreeSet::new();
        let mut pending = vec![(self.entry, sample_start)];
        while let Some((pattern, sample)) = pending.pop() {
            if let Some(&previous) = paired.get(&pattern) {
                if previous != sample {
                    return None;
                }
                continue;
            }
            if !copies.insert(sample) || self.blocks.contains(&sample) || body.contains(&sample) {
                return None;
            }
            paired.insert(pattern, sample);
            let expected = &graph.blocks[pattern];
            let actual = &graph.blocks[sample];
            let trim = pattern == self.tail;
            if (!trim || !self.tail_code.is_empty())
                && (routes[sample] != routes[pattern] || !actual.exception_predecessors.is_empty())
            {
                return None;
            }
            let start = expected.instructions.start + usize::from(pattern == handler);
            let end = if trim { self.tail_code.end } else { expected.instructions.end };
            let expected_code = &instructions[start..end];
            let actual_code = &instructions[actual.instructions.clone()];
            if actual_code.len() < expected_code.len()
                || !actual_code.iter().zip(expected_code).all(|(a, b)| same_instruction(a, b))
            {
                return None;
            }
            if trim {
                self.continuation = Some(sample);
            } else {
                if expected_code.len() != actual_code.len()
                    || expected.successors.len() != actual.successors.len()
                {
                    return None;
                }
                self.removed.insert(sample);
                pending.extend(expected.successors.iter().copied().zip(actual.successors.iter().copied()));
            }
        }
        let continuation = self.continuation?;
        for sample in self.removed.iter().copied().chain(
            (!self.tail_code.is_empty()).then_some(continuation),
        ) {
            if graph.blocks[sample].predecessors.iter().any(|pred| {
                !self.removed.contains(pred) && (sample != sample_start || !body.contains(pred))
            }) {
                return None;
            }
        }
        Some(())
    }
}

fn same_instruction(sample: &Instruction, pattern: &Instruction) -> bool {
    if sample.opcode != pattern.opcode
        && !(matches!(sample.opcode, 0xa7 | 0xc8) && matches!(pattern.opcode, 0xa7 | 0xc8))
    {
        return false;
    }
    match (&sample.operand, &pattern.operand) {
        (Operand::Branch(_), Operand::Branch(_)) => true,
        (Operand::Switch { default: a, cases: left }, Operand::Switch { default: b, cases: right }) => {
            if left.len() != right.len() {
                return false;
            }
            // The CFG orders each target by its first occurrence. Check the
            // case labels and the same equivalence classes of destinations,
            // including labels sharing the default destination.
            let mut left_to_right = BTreeMap::from([(*a, *b)]);
            let mut right_to_left = BTreeMap::from([(*b, *a)]);
            left.iter().zip(right).all(|(&(left_key, left), &(right_key, right))| {
                left_key == right_key
                    && *left_to_right.entry(left).or_insert(right) == right
                    && *right_to_left.entry(right).or_insert(left) == left
            })
        }
        (a, b) => a == b,
    }
}
