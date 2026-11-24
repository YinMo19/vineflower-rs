// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use std::collections::{BTreeMap, BTreeSet};

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
}

pub(in crate::structure) fn store(instruction: &Instruction) -> Option<Local> {
    local(instruction, 0x36, 0x3b)
}

pub(in crate::structure) fn returned(load: &Instruction, transfer: &Instruction) -> Option<Local> {
    let local = local(load, 0x15, 0x1a)?;
    (transfer.opcode == 0xac + local.category).then_some(local)
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
            if value.slots().any(|slot| reads(op, slot)) {
                return true;
            }
            if store(op).is_some_and(|written| value.slots().all(|slot| written.slots().any(|index| index == slot))) {
                continue 'walk;
            }
        }
        pending.extend_from_slice(&node.successors);
    }
    false
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
