// Copyright 2000-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

//! Expansion of JVM `jsr`, `jsr_w`, and `ret` before ordinary CFG construction.

use thiserror::Error;

use crate::bytecode::Instruction;
use crate::classfile::{ConstantPool, ExceptionHandler};

mod expand;
mod frame;

#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum LegacyError {
    #[error("invalid JVM subroutine at bytecode offset {offset}: {reason}")]
    Invalid { offset: u32, reason: &'static str },
    #[error("expanded JVM subroutine code exceeds the representable size")]
    CodeTooLong,
}

#[derive(Debug)]
pub struct NormalizedCode {
    pub instructions: Vec<Instruction>,
    pub handlers: Vec<ExceptionHandler>,
    // None avoids allocating a provenance table for methods without subroutines.
    origins: Option<Vec<Origin>>,
}

#[derive(Debug)]
struct Origin {
    start: u32,
    len: u32,
    source: u32,
}

impl NormalizedCode {
    /// Map a normalized byte offset to the original method's code array.
    /// Clones share source offsets. Inserted branch bytes without source bytes are unmapped.
    pub fn source_offset(&self, offset: u32) -> Option<u32> {
        match &self.origins {
            None => {
                let last = self.instructions.last()?;
                (offset < last.offset.checked_add(last.len)?).then_some(offset)
            }
            Some(origins) => {
                let index = origins.partition_point(|origin| origin.start <= offset);
                let origin = origins.get(index.checked_sub(1)?)?;
                let delta = offset - origin.start;
                (delta < origin.len).then_some(origin.source + delta)
            }
        }
    }
}

/// Clone reachable subroutine code for each calling context and resolve every
/// return address before passing the result to the CFG or expression lifter.
/// In the returned CFG input, offsets use instruction widths (and switch padding)
/// but are not an assembled bytecode stream: branch operands are absolute offsets.
/// The input must be the ordered instructions returned by `bytecode::decode`.
pub fn normalize(
    instructions: Vec<Instruction>,
    handlers: Vec<ExceptionHandler>,
    pool: &ConstantPool<'_>,
) -> Result<NormalizedCode, LegacyError> {
    if instructions
        .iter()
        .any(|op| matches!(op.opcode, 0xa8 | 0xa9 | 0xc9))
    {
        expand::expand(&instructions, &handlers, pool)
    } else {
        Ok(NormalizedCode {
            instructions,
            handlers,
            origins: None,
        })
    }
}

/// Word-level pop/push counts for instructions inside a straight-line proof.
/// The caller supplies the protected entry height; flow terminators cannot be
/// composed by this interface.
pub(crate) fn straight_line_stack_effect(
    op: &Instruction,
    pool: &ConstantPool<'_>,
) -> Option<(u16, u16)> {
    use frame::Effect;

    if matches!(op.opcode, 0x99..=0xb1 | 0xbf | 0xc6..=0xc9) {
        return None;
    }
    Some(match Effect::of(op, pool).ok()? {
        Effect::Ordinary { pop, push } => (pop, push),
        Effect::Read { width, .. } => (0, width),
        Effect::Write { width, .. } => (width, 0),
        Effect::Stack => match op.opcode {
            0x57 => (1, 0),
            0x58 => (2, 0),
            0x59 => (1, 2),
            0x5a => (2, 3),
            0x5b => (3, 4),
            0x5c => (2, 4),
            0x5d => (3, 5),
            0x5e => (4, 6),
            0x5f => (2, 2),
            _ => return None,
        },
    })
}

fn invalid(offset: u32, reason: &'static str) -> LegacyError {
    LegacyError::Invalid { offset, reason }
}

#[cfg(test)]
mod tests;
