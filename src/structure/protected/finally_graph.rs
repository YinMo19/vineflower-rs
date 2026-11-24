// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use std::collections::{BTreeMap, BTreeSet};
use std::ops::Range;

use crate::bytecode::{Instruction, Operand};
use crate::cfg::ControlFlowGraph;

use super::monitor::MonitorPlan;
use super::{Route, local_touches, normal_exits, reference_load, reference_store};

pub(in crate::structure) struct BranchedFinally {
    pub(in crate::structure) entry: usize,
    pub(in crate::structure) continuation: Option<usize>,
    pub(in crate::structure) removed: BTreeSet<usize>,
    pub(super) blocks: BTreeSet<usize>,
    pub(super) body_join: Option<usize>,
    pub(super) projected_entries: BTreeSet<usize>,
    pub(super) prefix_block: Option<usize>,
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
        monitors: &BTreeMap<usize, &MonitorPlan>,
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
        let monitor = monitors.get(&entry).copied();
        let mut cleanup = BTreeSet::new();
        let mut rethrow = None;
        let mut pending = vec![entry];
        while let Some(index) = pending.pop() {
            if !cleanup.insert(index) {
                continue;
            }
            let block = &graph.blocks[index];
            if body.contains(&index)
                || (index != handler && !block.exception_predecessors.is_empty())
            {
                return None;
            }
            let start = block.instructions.start + usize::from(index == handler);
            let mut end = block.instructions.end;
            if let [.., load, throw] = &instructions[start..end]
                && reference_load(load) == Some(slot)
                && throw.opcode == 0xbf
            {
                end -= 2;
                if rethrow.replace((index, start..end)).is_some() {
                    return None;
                }
            }
            if instructions[start..end]
                .iter()
                .any(|op| local_touches(op, slot))
            {
                return None;
            }
            pending.extend(block.successors.iter().copied());
        }
        let (tail, tail_code) = rethrow?;
        if entry == tail {
            return None;
        }
        cleanup.insert(handler);
        if let Some(monitor) = monitor {
            for block in monitor.handler_blocks() {
                if body.contains(&block)
                    || !cleanup.insert(block)
                    || instructions[graph.blocks[block].instructions.clone()]
                        .iter()
                        .any(|op| local_touches(op, slot))
                {
                    return None;
                }
            }
            if monitor.handler_blocks().any(|block| {
                graph.blocks[block]
                    .exception_predecessors
                    .iter()
                    .any(|pred| !cleanup.contains(pred))
            }) {
                return None;
            }
        }
        if cleanup.iter().any(|&block| {
            graph.blocks[block]
                .predecessors
                .iter()
                .any(|pred| !cleanup.contains(pred))
        }) || body.iter().any(|&block| {
            matches!(
                instructions[graph.blocks[block].instructions.end - 1].opcode,
                0xac..=0xb1
            )
        }) {
            return None;
        }
        let exits: BTreeSet<_> = normal_exits(graph, body).collect();
        let mut result = Self {
            entry,
            continuation: None,
            removed: BTreeSet::new(),
            blocks: cleanup,
            body_join: None,
            projected_entries: BTreeSet::new(),
            prefix_block: None,
            tail,
            tail_code,
        };
        let mut tails = BTreeSet::new();
        for &sample in &exits {
            let pair = match (monitor, monitors.get(&sample).copied()) {
                (Some(pattern), Some(sample)) => Some(MonitorCopy { pattern, sample }),
                (None, None) => None,
                _ => return None,
            };
            let (tail, removed) =
                result.match_copy(instructions, graph, routes, body, handler, sample, pair)?;
            tails.insert(tail);
            for block in removed {
                if !result.removed.insert(block) {
                    return None;
                }
            }
        }
        if !result.tail_code.is_empty()
            && tails.iter().any(|&tail| {
                graph.blocks[tail]
                    .predecessors
                    .iter()
                    .any(|pred| !result.removed.contains(pred))
            })
        {
            return None;
        }
        if tails.len() == 1 {
            let tail = tails.pop_first()?;
            result.continuation = Some(tail);
            result.prefix_block = Some(tail);
        } else if !tails.is_empty() {
            // Distinct final blocks can still finish at the same source
            // continuation, with separate goto stubs from the inliner.
            let mut continuation = None;
            for tail in tails {
                let node = &graph.blocks[tail];
                let &[next] = node.successors.as_slice() else {
                    return None;
                };
                let start = node.instructions.start + result.tail_code.len();
                let [jump] = &instructions[start..node.instructions.end] else {
                    return None;
                };
                if !matches!(jump.opcode, 0xa7 | 0xc8)
                    || !node.exception_predecessors.is_empty()
                    || node
                        .predecessors
                        .iter()
                        .any(|pred| !result.removed.contains(pred))
                    || continuation.is_some_and(|target| target != next)
                {
                    return None;
                }
                continuation = Some(next);
                if !result.removed.insert(tail) {
                    return None;
                }
            }
            result.continuation = continuation;
        }
        if result
            .continuation
            .is_some_and(|next| result.removed.contains(&next))
        {
            return None;
        }
        if exits.len() > 1 {
            result.body_join = result.continuation;
            result.projected_entries = exits;
        } else {
            result.body_join = exits.first().copied();
        }
        Some(result)
    }

    fn match_copy(
        &self,
        instructions: &[Instruction],
        graph: &ControlFlowGraph,
        routes: &[Vec<Route>],
        body: &BTreeSet<usize>,
        handler: usize,
        sample_start: usize,
        monitor: Option<MonitorCopy<'_>>,
    ) -> Option<(usize, BTreeSet<usize>)> {
        let mut paired = BTreeMap::new();
        let mut copies = BTreeSet::new();
        let mut removed = BTreeSet::new();
        let mut continuation = None;
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
                && (!actual.exception_predecessors.is_empty()
                    || !same_dispatch(&routes[pattern], &routes[sample], monitor))
            {
                return None;
            }
            let start = expected.instructions.start + usize::from(pattern == handler);
            let end = if trim {
                self.tail_code.end
            } else {
                expected.instructions.end
            };
            let mut expected_code = &instructions[start..end];
            let mut actual_code = &instructions[actual.instructions.clone()];
            if !trim && expected.successors.len() == 1 && actual.successors.len() == 1 {
                // An inlined cleanup can jump over the exception handler
                // where the handler's copy simply falls through. The
                // successor pairing below proves the corresponding target.
                expected_code = before_unconditional_jump(expected_code);
                actual_code = before_unconditional_jump(actual_code);
            }
            if let Some(copy) = monitor {
                (expected_code, actual_code) =
                    copy.source_code(instructions, pattern, sample, expected_code, actual_code)?;
            }
            if actual_code.len() < expected_code.len()
                || !actual_code
                    .iter()
                    .zip(expected_code)
                    .all(|(a, b)| same_instruction(a, b))
            {
                return None;
            }
            if trim {
                continuation = Some(sample);
            } else {
                if expected_code.len() != actual_code.len()
                    || expected.successors.len() != actual.successors.len()
                {
                    return None;
                }
                removed.insert(sample);
                pending.extend(
                    expected
                        .successors
                        .iter()
                        .copied()
                        .zip(actual.successors.iter().copied()),
                );
            }
        }
        if let Some(copy) = monitor {
            if copy.pattern.handler_blocks().count() != copy.sample.handler_blocks().count()
                || copy.pattern.handler.has_self_protected_prefix()
                    != copy.sample.handler.has_self_protected_prefix()
            {
                return None;
            }
            for (pattern, sample) in copy.pattern.handler_blocks().zip(copy.sample.handler_blocks())
            {
                let pattern_block = &graph.blocks[pattern];
                let sample_block = &graph.blocks[sample];
                if self.blocks.contains(&sample)
                    || body.contains(&sample)
                    || !copies.insert(sample)
                    || !removed.insert(sample)
                    || !same_dispatch(&routes[pattern], &routes[sample], monitor)
                    || pattern_block.exception_successors.contains(&copy.pattern.handler.start)
                        != sample_block.exception_successors.contains(&copy.sample.handler.start)
                {
                    return None;
                }
            }
            if copy.sample.handler_blocks().any(|block| {
                graph.blocks[block]
                    .exception_predecessors
                    .iter()
                    .any(|pred| !removed.contains(pred))
            }) {
                return None;
            }
        }
        for &sample in &removed {
            if graph.blocks[sample].predecessors.iter().any(|pred| {
                !removed.contains(pred) && (sample != sample_start || !body.contains(pred))
            }) {
                return None;
            }
        }
        Some((continuation?, removed))
    }
}

#[derive(Clone, Copy)]
struct MonitorCopy<'a> {
    pattern: &'a MonitorPlan,
    sample: &'a MonitorPlan,
}

impl MonitorCopy<'_> {
    fn source_code<'a>(
        self,
        instructions: &[Instruction],
        pattern: usize,
        sample: usize,
        mut expected: &'a [Instruction],
        mut actual: &'a [Instruction],
    ) -> Option<(&'a [Instruction], &'a [Instruction])> {
        if pattern == self.pattern.acquisition {
            if sample != self.sample.acquisition {
                return None;
            }
            expected = expected.get(..expected.len().checked_sub(self.pattern.scaffold.len())?)?;
            actual = actual.get(..actual.len().checked_sub(self.sample.scaffold.len())?)?;
        } else if sample == self.sample.acquisition {
            return None;
        }
        match (self.pattern.releases.get(&pattern), self.sample.releases.get(&sample)) {
            (Some(release), Some(copy))
                if expected.last()?.offset == instructions[release.end - 1].offset
                    && actual.last()?.offset == instructions[copy.end - 1].offset =>
            {
                // Only the confirmed synthetic releases may differ in their
                // local slot. The acquisition expressions and body stay exact.
                expected = &expected[..expected.len().checked_sub(release.len())?];
                actual = &actual[..actual.len().checked_sub(copy.len())?];
            }
            (None, None) => {}
            _ => return None,
        }
        Some((expected, actual))
    }
}

fn same_dispatch(pattern: &[Route], sample: &[Route], monitor: Option<MonitorCopy<'_>>) -> bool {
    pattern.len() == sample.len()
        && pattern.iter().zip(sample).all(|(pattern, sample)| {
            if let Some(copy) = monitor
                && pattern.handler == copy.pattern.handler.start
            {
                pattern.catch_type == 0
                    && sample.catch_type == 0
                    && sample.handler == copy.sample.handler.start
            } else {
                pattern == sample
            }
        })
}

fn before_unconditional_jump(code: &[Instruction]) -> &[Instruction] {
    match code {
        [body @ .., last] if matches!(last.opcode, 0xa7 | 0xc8) => body,
        _ => code,
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
        (
            Operand::Switch {
                default: a,
                cases: left,
            },
            Operand::Switch {
                default: b,
                cases: right,
            },
        ) => {
            if left.len() != right.len() {
                return false;
            }
            // The CFG orders each target by its first occurrence. Check the
            // case labels and the same equivalence classes of destinations,
            // including labels sharing the default destination.
            let mut left_to_right = BTreeMap::from([(*a, *b)]);
            let mut right_to_left = BTreeMap::from([(*b, *a)]);
            left.iter()
                .zip(right)
                .all(|(&(left_key, left), &(right_key, right))| {
                    left_key == right_key
                        && *left_to_right.entry(left).or_insert(right) == right
                        && *right_to_left.entry(right).or_insert(left) == left
                })
        }
        (a, b) => a == b,
    }
}
