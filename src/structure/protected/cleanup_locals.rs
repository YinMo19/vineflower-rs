// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use std::collections::{BTreeMap, BTreeSet};
use std::ops::Range;

use crate::bytecode::{Instruction, Operand};
use crate::cfg::ControlFlowGraph;

#[derive(Clone, Copy, Eq, PartialEq)]
pub(in crate::structure) struct Local {
    slot: u16,
    category: u8,
}

impl Local {
    fn new(slot: u16, category: u8) -> Option<Self> {
        (slot != u16::MAX || !matches!(category, 1 | 3)).then_some(Self { slot, category })
    }

    pub(in crate::structure) fn slots(self) -> impl Iterator<Item = u16> {
        std::iter::once(self.slot).chain(
            matches!(self.category, 1 | 3)
                .then(|| self.slot.checked_add(1))
                .flatten(),
        )
    }

    pub(in crate::structure) fn touches(self, instruction: &Instruction) -> bool {
        self.slots()
            .any(|slot| super::local_touches(instruction, slot))
    }

    fn overlaps(self, other: Self) -> bool {
        self.slots().any(|slot| other.slots().any(|lane| lane == slot))
    }

    fn covered_by(self, written: Self) -> bool {
        self.slots().all(|slot| written.slots().any(|lane| lane == slot))
    }
}

pub(in crate::structure) fn store(instruction: &Instruction) -> Option<Local> {
    local(instruction, 0x36, 0x3b)
}

pub(in crate::structure) fn returned(load: &Instruction, transfer: &Instruction) -> Option<Local> {
    let local = local(load, 0x15, 0x1a)?;
    (transfer.opcode == 0xac + local.category).then_some(local)
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum Operation {
    Load,
    Store,
    Increment(i16),
}

fn access(instruction: &Instruction) -> Option<(Local, Operation)> {
    if let Operand::Increment { index, amount } = instruction.operand {
        return Some((Local::new(index, 0)?, Operation::Increment(amount)));
    }
    if let Some(local) = local(instruction, 0x15, 0x1a) {
        return Some((local, Operation::Load));
    }
    store(instruction).map(|local| (local, Operation::Store))
}

#[derive(Default)]
pub(super) struct Renames(Vec<(Local, Local)>);

impl Renames {
    pub(super) fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub(super) fn match_access(&mut self, pattern: &Instruction, copy: &Instruction) -> bool {
        let (Some((left, a)), Some((right, b))) = (access(pattern), access(copy)) else {
            return false;
        };
        if a != b || left.category != right.category {
            return false;
        }
        if left == right {
            return true;
        }
        if let Some(&pair) = self.0.iter().find(|(a, b)| a.overlaps(left) || b.overlaps(right)) {
            return pair == (left, right);
        }
        self.0.push((left, right));
        true
    }

    pub(super) fn keeps_bijection(&self, pattern: &Instruction, copy: &Instruction) -> bool {
        self.0.iter().all(|&(left, right)| {
            if left.touches(pattern) || right.touches(copy) {
                match (access(pattern), access(copy)) {
                    (Some((a, x)), Some((b, y))) => a == left && b == right && x == y,
                    _ => false,
                }
            } else {
                true
            }
        })
    }

    pub(super) fn pairs(&self) -> impl Iterator<Item = (Local, Local)> + '_ {
        self.0.iter().copied()
    }
}

pub(super) fn binding_slot(instruction: &Instruction) -> Option<Local> {
    let local = store(instruction)?;
    (local.category == 4).then_some(local)
}

/// Locals (including either half of a wide value) read by an instruction.
pub(super) fn reads(instruction: &Instruction, slot: u16) -> bool {
    match instruction.operand {
        Operand::Increment { index, .. } => index == slot,
        _ => local(instruction, 0x15, 0x1a).is_some_and(|read| read.slots().any(|index| index == slot)),
    }
}

pub(super) fn live_at_any(
    instructions: &[Instruction],
    graph: &ControlFlowGraph,
    starts: &BTreeSet<usize>,
    value: Local,
) -> bool {
    let mut pending: Vec<_> = starts.iter().copied().collect();
    let mut seen = BTreeSet::new();
    'walk: while let Some(block) = pending.pop() {
        if !seen.insert(block) {
            continue;
        }
        let node = &graph.blocks[block];
        // Conservatively keep the incoming value on exceptional edges.
        pending.extend_from_slice(&node.exception_successors);
        for op in &instructions[node.instructions.clone()] {
            match local_access(op, value) {
                Some(true) => return true,
                Some(false) => continue 'walk,
                None => {}
            }
        }
        pending.extend_from_slice(&node.successors);
    }
    false
}

fn local_access(instruction: &Instruction, value: Local) -> Option<bool> {
    if value.slots().any(|slot| reads(instruction, slot)) {
        Some(true)
    } else if store(instruction).is_some_and(|written| value.covered_by(written)) {
        Some(false)
    } else {
        None
    }
}

/// A private copy binding is written before any use in its matched code.
/// No normal or exceptional departure can observe the last value written.
pub(super) fn private_copy_local(
    instructions: &[Instruction],
    graph: &ControlFlowGraph,
    ranges: &BTreeMap<usize, Range<usize>>,
    entry: usize,
    value: Local,
) -> bool {
    let first_access = |range: Range<usize>| {
        instructions[range].iter().find_map(|op| local_access(op, value))
    };
    let mut seen = BTreeSet::new();
    let mut pending = vec![entry];
    while let Some(block) = pending.pop() {
        if !seen.insert(block) {
            continue;
        }
        let node = &graph.blocks[block];
        let range = &ranges[&block];
        pending.extend(node.exception_successors.iter().copied().filter(|target| ranges.contains_key(target)));
        match first_access(range.clone()) {
            Some(true) => return false,
            Some(false) => {}
            None if range.end == node.instructions.end => {
                pending.extend(node.successors.iter().copied().filter(|target| ranges.contains_key(target)));
            }
            None => {}
        }
    }
    dead_after_copy(instructions, graph, ranges, value)
}

pub(super) fn dead_after_copy(
    instructions: &[Instruction],
    graph: &ControlFlowGraph,
    ranges: &BTreeMap<usize, Range<usize>>,
    value: Local,
) -> bool {
    let mut exits = BTreeSet::new();
    for (&block, range) in ranges {
        let node = &graph.blocks[block];
        exits.extend(node.exception_successors.iter().copied().filter(|target| !ranges.contains_key(target)));
        let suffix = &instructions[range.end..node.instructions.end];
        match suffix.iter().find_map(|op| local_access(op, value)) {
            Some(true) => return false,
            Some(false) => {}
            None => exits.extend(node.successors.iter().copied().filter(|target| {
                range.end != node.instructions.end || !ranges.contains_key(target)
            })),
        }
    }
    !live_at_any(instructions, graph, &exits, value)
}

fn local(instruction: &Instruction, indexed: u8, implicit: u8) -> Option<Local> {
    match instruction.opcode {
        op if (indexed..indexed + 5).contains(&op) => {
            let Operand::Local(slot) = instruction.operand else {
                return None;
            };
            Local::new(slot, op - indexed)
        }
        op if (implicit..implicit + 20).contains(&op) => {
            Local::new(u16::from((op - implicit) % 4), (op - implicit) / 4)
        }
        _ => None,
    }
}

pub(super) fn same_cleanup(
    all: &[Instruction],
    pattern: &[Instruction],
    copy: &[Instruction],
) -> bool {
    fn exact(a: &Instruction, b: &Instruction) -> bool {
        a.opcode == b.opcode && a.operand == b.operand
    }
    if pattern.len() != copy.len() {
        return false;
    }
    if pattern.iter().zip(copy).all(|(a, b)| exact(a, b)) {
        return true;
    }
    let mut from = BTreeMap::new();
    let mut to = BTreeMap::new();
    let mut renamed = BTreeSet::new();
    for (a, b) in pattern.iter().zip(copy) {
        if let (Some(a), Some(b)) = (store(a), store(b)) {
            if a.category != b.category {
                return false;
            }
            for (left, right) in a.slots().zip(b.slots()) {
                if *from.entry(left).or_insert(right) != right
                    || *to.entry(right).or_insert(left) != left
                {
                    return false;
                }
                if left != right {
                    renamed.extend([left, right]);
                }
            }
        } else if !exact(a, b) {
            return false;
        }
    }
    // A copied finally can use different JVM slots for stores to private
    // temporaries. Only permit renaming cells whose values cannot be read
    // on any path, including exception handlers and category-2 aliases.
    renamed.is_empty()
        || !all.iter().any(|op| match op.operand {
            Operand::Increment { index, .. } => renamed.contains(&index),
            _ => local(op, 0x15, 0x1a)
                .is_some_and(|read| read.slots().any(|slot| renamed.contains(&slot))),
        })
}
