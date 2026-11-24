// Based on Vineflower InitializerProcessor (Apache-2.0).
use std::ops::Range;

use crate::{
    bytecode::{Instruction, Operand},
    lift::{Effect, Machine},
};

/// A closed javac boolean materialization followed immediately by its store.
/// The enclosing scan separately checks incoming edges and exception coverage.
pub(super) struct BooleanTail<'i> {
    branch: &'i Instruction,
    fallthrough: &'i Instruction,
    taken: &'i Instruction,
    pub(super) store: &'i Instruction,
}

impl<'i> BooleanTail<'i> {
    pub(super) const STORE_INDEX: usize = 4;

    pub(super) fn read(instructions: &'i [Instruction]) -> Option<Self> {
        let [branch, fallthrough, jump, taken, store, ..] = instructions else {
            return None;
        };
        if !matches!(branch.opcode, 0x99..=0xa6 | 0xc6..=0xc7)
            || branch.operand != Operand::Branch(taken.offset)
            || !matches!((fallthrough.opcode, taken.opcode), (0x03, 0x04) | (0x04, 0x03))
            || !matches!(jump.opcode, 0xa7 | 0xc8)
            || jump.operand != Operand::Branch(store.offset)
            || !matches!(store.opcode, 0xb3 | 0xb5)
        {
            return None;
        }
        Some(Self { branch, fallthrough, taken, store })
    }

    pub(super) fn lift(&self, machine: &mut Machine<'_, '_>, start: u32) -> Option<Range<u32>> {
        let Effect::Branch { when_true, when_false, .. } = machine.step(self.branch).ok()? else {
            return None;
        };
        if !machine.take_prelude().is_empty() {
            return None;
        }
        let mut taken = machine.clone();
        let mut fallthrough = machine.clone();
        if !matches!(taken.step(self.taken).ok()?, Effect::None)
            || !matches!(fallthrough.step(self.fallthrough).ok()?, Effect::None)
        {
            return None;
        }
        let condition = (&when_true, &when_false, machine.last_boolean_condition());
        let control = start..=self.branch.offset + self.branch.len - 1;
        machine
            .merge_conditional_stack(&taken, &fallthrough, condition, &control, None)
            .ok()
            .flatten()?;
        Some(self.fallthrough.offset..self.store.offset)
    }
}
