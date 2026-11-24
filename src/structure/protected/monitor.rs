// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use std::collections::{BTreeMap, BTreeSet};
use std::ops::Range;

use crate::bytecode::Instruction;
use crate::cfg::ControlFlowGraph;

use super::{local_touches, reference_load, reference_store};

#[derive(Clone, Copy)]
pub(super) struct MonitorHandler {
    pub(super) start: usize,
    release: usize,
    pub(super) rethrow: usize,
    throwable: Option<u16>,
    slot: u16,
}

pub(in crate::structure) struct MonitorPlan {
    pub(super) acquisition: usize,
    pub(super) scaffold: Range<usize>,
    pub(super) releases: BTreeMap<usize, Range<usize>>,
    pub(super) handler: MonitorHandler,
}

impl MonitorHandler {
    pub(super) fn detect(
        instructions: &[Instruction],
        graph: &ControlFlowGraph,
        start: usize,
    ) -> Option<Self> {
        let entry = &graph.blocks[start];
        if start == 0 || !entry.predecessors.is_empty() {
            return None;
        }
        let mut code = &instructions[entry.instructions.clone()];
        let (release, exception) = if let [store] = code
            && let Some(slot) = reference_store(store)
        {
            // Kotlin can protect only the handler's initial astore.
            let next = exclusive_successor(graph, start)?;
            code = &instructions[graph.blocks[next].instructions.clone()];
            (next, Some(slot))
        } else if let [store, rest @ ..] = code
            && let Some(slot) = reference_store(store)
        {
            code = rest;
            (start, Some(slot))
        } else {
            (start, None)
        };
        let [lock, exit, suffix @ ..] = code else {
            return None;
        };
        if exit.opcode != 0xc3 {
            return None;
        }
        let released = reference_load(lock)?;
        if exception == Some(released) {
            return None;
        }
        let (rethrow, suffix) = if suffix.is_empty() {
            let next = exclusive_successor(graph, release)?;
            (next, &instructions[graph.blocks[next].instructions.clone()])
        } else {
            (release, suffix)
        };
        match (exception, suffix) {
            (Some(exception), [load, throw])
                if reference_load(load) == Some(exception) && throw.opcode == 0xbf => {}
            (None, [throw]) if throw.opcode == 0xbf => {}
            _ => return None,
        }
        graph.blocks[rethrow].successors.is_empty().then_some(Self {
            start,
            release,
            rethrow,
            throwable: exception,
            slot: released,
        })
    }

    pub(super) fn has_self_protected_prefix(&self) -> bool {
        // The edge retries the release only. Including the rethrow itself
        // would change exception dispatch, not just guard a compiler epilogue.
        self.start == self.release && self.start != self.rethrow
    }

    fn blocks(&self) -> impl Iterator<Item = usize> {
        std::iter::once(self.start)
            .chain((self.release != self.start).then_some(self.release))
            .chain((self.rethrow != self.release).then_some(self.rethrow))
    }
}

fn exclusive_successor(graph: &ControlFlowGraph, block: usize) -> Option<usize> {
    let &[next] = graph.blocks[block].successors.as_slice() else {
        return None;
    };
    let next_block = &graph.blocks[next];
    (next_block.predecessors == [block] && next_block.exception_predecessors.is_empty())
        .then_some(next)
}

impl MonitorPlan {
    pub(super) fn prove(
        instructions: &[Instruction],
        graph: &ControlFlowGraph,
        body: &BTreeSet<usize>,
        handler: MonitorHandler,
    ) -> Option<Self> {
        if handler.blocks().any(|block| body.contains(&block)) {
            return None;
        }
        let slot = handler.slot;
        let mut heads = body.iter().filter_map(|&block| {
            graph.blocks[block]
                .predecessors
                .iter()
                .copied()
                .find(|&pred| {
                    !body.contains(&pred)
                        && graph.blocks[pred].successors == [block]
                        && instructions[graph.blocks[pred].instructions.end - 1].opcode == 0xc2
                })
                .map(|pred| (block, pred))
        });
        let (head, acquisition) = heads.next()?;
        if heads.next().is_some()
            || !graph.blocks[head]
                .predecessors
                .iter()
                .copied()
                .filter(|pred| !body.contains(pred))
                .eq(std::iter::once(acquisition))
            || graph.blocks[head]
                .exception_predecessors
                .iter()
                .any(|pred| !body.contains(pred))
        {
            return None;
        }
        let range = &graph.blocks[acquisition].instructions;
        let scaffold = range.end.checked_sub(3)?..range.end;
        if scaffold.start < range.start {
            return None;
        }
        let [first, second, _enter] = &instructions[scaffold.clone()] else {
            return None;
        };
        if !(first.opcode == 0x59 && reference_store(second) == Some(slot)
            || reference_store(first) == Some(slot) && reference_load(second) == Some(slot))
        {
            return None;
        }

        let mut releases = BTreeMap::new();
        let mut unlocked = BTreeSet::new();
        for &block in body {
            let node = &graph.blocks[block];
            let range = node.instructions.clone();
            let code = &instructions[range.clone()];
            let release = release_of(code, slot)?;
            if let Some(release) = release {
                if node.successors.iter().any(|next| body.contains(next)) {
                    return None;
                }
                releases.insert(block, range.start + release..range.start + release + 2);
                unlocked.extend(node.successors.iter().copied());
                continue;
            }
            if matches!(code.last()?.opcode, 0xac..=0xb1) {
                // Every returning path must have released the monitor.
                return None;
            }
            for &next in &node.successors {
                if body.contains(&next) {
                    continue;
                }
                let outside = &graph.blocks[next];
                let range = outside.instructions.clone();
                if !outside.exception_predecessors.is_empty()
                    || outside.predecessors.iter().any(|pred| !body.contains(pred))
                    || outside
                        .successors
                        .iter()
                        .any(|successor| body.contains(successor))
                    || release_of(&instructions[range.clone()], slot)? != Some(0)
                {
                    return None;
                }
                releases.insert(next, range.start..range.start + 2);
                unlocked.extend(outside.successors.iter().copied());
            }
        }
        if unlocked.iter().any(|block| releases.contains_key(block)) {
            return None;
        }
        unlocked.extend(
            graph.blocks[handler.rethrow]
                .exception_successors
                .iter()
                .copied(),
        );
        unlocked.extend(graph.blocks[acquisition].exception_successors.iter().copied());
        if escapes(instructions, graph, slot, unlocked)
            || handler.throwable.is_some_and(|throwable| {
                escapes(
                    instructions,
                    graph,
                    throwable,
                    graph.blocks[handler.rethrow]
                        .exception_successors
                        .iter()
                        .copied()
                        .collect(),
                )
            })
        {
            return None;
        }
        Some(Self {
            acquisition,
            scaffold,
            releases,
            handler,
        })
    }

    pub(in crate::structure) fn enter_index(&self) -> usize {
        self.scaffold.end - 1
    }

    pub(in crate::structure) fn release_index(&self, block: usize) -> Option<usize> {
        self.releases.get(&block).map(|release| release.end - 1)
    }

    pub(in crate::structure) fn handler_blocks(&self) -> impl Iterator<Item = usize> {
        self.handler.blocks()
    }
}

// A release is always a net-zero stack operation, possibly on top of an
// already computed return value. Nothing except the transfer may follow it
// in the same block. Other uses of the synthetic lock local are observable.
fn release_of(code: &[Instruction], slot: u16) -> Option<Option<usize>> {
    let mut release = None;
    for (index, instruction) in code.iter().enumerate() {
        if !local_touches(instruction, slot) {
            continue;
        }
        if release.is_some()
            || reference_load(instruction) != Some(slot)
            || code.get(index + 1)?.opcode != 0xc3
            || !matches!(
                &code[index + 2..],
                [] | [Instruction {
                    opcode: 0xa7 | 0xc8 | 0xac..=0xb1,
                    ..
                }]
            )
        {
            return None;
        }
        release = Some(index);
    }
    Some(release)
}

fn escapes(
    instructions: &[Instruction],
    graph: &ControlFlowGraph,
    slot: u16,
    starts: BTreeSet<usize>,
) -> bool {
    let mut pending: Vec<_> = starts.into_iter().collect();
    let mut seen = vec![false; graph.blocks.len()];
    while let Some(block) = pending.pop() {
        if std::mem::replace(&mut seen[block], true) {
            continue;
        }
        let node = &graph.blocks[block];
        match instructions[node.instructions.clone()]
            .iter()
            .find(|op| local_touches(op, slot))
        {
            Some(op) if matches!(op.opcode, 0x36..=0x4e) => {}
            Some(_) => return true,
            None => pending.extend(node.successors.iter().copied()),
        }
        // An exceptional edge can be taken before the overwrite.
        pending.extend(node.exception_successors.iter().copied());
    }
    false
}
