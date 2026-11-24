use std::ops::Range;

use thiserror::Error;

use crate::bytecode::{Instruction, Operand};
use crate::classfile::ExceptionHandler;

mod analysis;

pub use analysis::NaturalLoop;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Error)]
pub enum CfgError {
    #[error(
        "legacy JVM subroutine opcode {opcode:#04x} at bytecode offset {offset} is not supported"
    )]
    LegacySubroutine { offset: u32, opcode: u8 },
    #[error("invalid control-flow operand for opcode {opcode:#04x} at bytecode offset {offset}")]
    InvalidOperand { offset: u32, opcode: u8 },
    #[error("bytecode offset {offset} is not an instruction boundary")]
    InvalidTarget { offset: u32 },
    #[error("invalid protected bytecode range {start}..{end}")]
    InvalidProtectedRange { start: u32, end: u32 },
    #[error("instruction at bytecode offset {offset} falls through the end of the method")]
    MissingFallthrough { offset: u32 },
}

#[derive(Debug)]
pub struct Block {
    /// Indices into the original decoded instruction slice.
    pub instructions: Range<usize>,
    /// Normal destinations, in branch-target then fallthrough order for conditionals.
    pub successors: Vec<usize>,
    pub predecessors: Vec<usize>,
    /// Conservative edges for every block covered by an exception handler, in table order.
    pub exception_successors: Vec<usize>,
    pub exception_predecessors: Vec<usize>,
}

#[derive(Debug)]
pub struct ControlFlowGraph {
    /// Blocks in bytecode order; block 0 is the method entry if there are any blocks.
    pub blocks: Vec<Block>,
    block_offsets: Vec<u32>,
}

enum Transfer<'a> {
    Next,
    Conditional(u32),
    Jump(u32),
    Switch(u32, &'a [(i32, u32)]),
    Stop,
}

impl<'a> Transfer<'a> {
    fn of(instruction: &'a Instruction) -> Result<Self, CfgError> {
        let Instruction { offset, opcode, .. } = *instruction;
        let invalid = || CfgError::InvalidOperand { offset, opcode };
        match opcode {
            0xa8 | 0xa9 | 0xc9 => Err(CfgError::LegacySubroutine { offset, opcode }),
            0x99..=0xa6 | 0xc6 | 0xc7 => match &instruction.operand {
                Operand::Branch(target) => Ok(Self::Conditional(*target)),
                _ => Err(invalid()),
            },
            0xa7 | 0xc8 => match &instruction.operand {
                Operand::Branch(target) => Ok(Self::Jump(*target)),
                _ => Err(invalid()),
            },
            0xaa | 0xab => match &instruction.operand {
                Operand::Switch { default, cases } => Ok(Self::Switch(*default, cases)),
                _ => Err(invalid()),
            },
            0xac..=0xb1 | 0xbf => Ok(Self::Stop),
            _ => Ok(Self::Next),
        }
    }

    fn targets(&self) -> impl Iterator<Item = u32> + '_ {
        let (first, cases) = match *self {
            Self::Conditional(target) | Self::Jump(target) => (Some(target), &[][..]),
            Self::Switch(default, cases) => (Some(default), cases),
            Self::Next | Self::Stop => (None, &[][..]),
        };
        first
            .into_iter()
            .chain(cases.iter().map(|&(_, target)| target))
    }
}

impl ControlFlowGraph {
    /// The caller establishes a void method without exception handlers or
    /// legacy subroutines. The synthetic return has no original source bytes.
    pub(crate) fn complete_void_tail(instructions: &mut Vec<Instruction>) {
        if let Some(last) = instructions.last()
            && matches!(Transfer::of(last), Ok(Transfer::Next | Transfer::Conditional(_)))
            && let Some(offset) = last.offset.checked_add(last.len)
        {
            instructions.push(Instruction { offset, opcode: 0xb1, operand: Operand::None, len: 0 });
        }
    }

    pub fn build(
        instructions: &[Instruction],
        handlers: &[ExceptionHandler],
    ) -> Result<Self, CfgError> {
        let mut leaders = vec![false; instructions.len()];
        if let Some(first) = leaders.first_mut() {
            *first = true;
        }
        let instruction_index = |offset| {
            instructions
                .binary_search_by_key(&offset, |instruction| instruction.offset)
                .map_err(|_| CfgError::InvalidTarget { offset })
        };
        for (i, instruction) in instructions.iter().enumerate() {
            let transfer = Transfer::of(instruction)?;
            for target in transfer.targets() {
                leaders[instruction_index(target)?] = true;
            }
            if let Some(next) = leaders.get_mut(i + 1) {
                *next |= !matches!(transfer, Transfer::Next);
            } else if matches!(transfer, Transfer::Next | Transfer::Conditional(_)) {
                return Err(CfgError::MissingFallthrough {
                    offset: instruction.offset,
                });
            }
        }

        let code_end = instructions
            .last()
            .and_then(|last| last.offset.checked_add(last.len));
        for handler in handlers {
            let start = u32::from(handler.start_pc);
            let end = u32::from(handler.end_pc);
            if start >= end {
                return Err(CfgError::InvalidProtectedRange { start, end });
            }
            leaders[instruction_index(start)?] = true;
            if Some(end) != code_end {
                leaders[instruction_index(end)?] = true;
            }
            leaders[instruction_index(u32::from(handler.handler_pc))?] = true;
        }

        let mut starts = leaders
            .into_iter()
            .enumerate()
            .filter_map(|(i, leader)| leader.then_some(i))
            .peekable();
        let mut blocks = Vec::new();
        let mut block_offsets = Vec::new();
        while let Some(start) = starts.next() {
            let end = starts.peek().copied().unwrap_or(instructions.len());
            blocks.push(Block {
                instructions: start..end,
                successors: Vec::new(),
                predecessors: Vec::new(),
                exception_successors: Vec::new(),
                exception_predecessors: Vec::new(),
            });
            block_offsets.push(instructions[start].offset);
        }
        let block_index = |offset| {
            block_offsets
                .binary_search(&offset)
                .map_err(|_| CfgError::InvalidTarget { offset })
        };
        let mut normal_seen = vec![usize::MAX; blocks.len()];
        for source in 0..blocks.len() {
            let transfer = Transfer::of(&instructions[blocks[source].instructions.end - 1])?;
            let mut add_edge = |destination: usize| {
                if normal_seen[destination] != source {
                    normal_seen[destination] = source;
                    blocks[source].successors.push(destination);
                    blocks[destination].predecessors.push(source);
                }
            };
            for target in transfer.targets() {
                add_edge(block_index(target)?);
            }
            if matches!(transfer, Transfer::Next | Transfer::Conditional(_)) {
                add_edge(source + 1);
            }
        }
        for handler in handlers {
            let start = block_index(u32::from(handler.start_pc))?;
            let end = if Some(u32::from(handler.end_pc)) == code_end {
                blocks.len()
            } else {
                block_index(u32::from(handler.end_pc))?
            };
            let destination = block_index(u32::from(handler.handler_pc))?;
            for source in start..end {
                if !blocks[source].exception_successors.contains(&destination) {
                    blocks[source].exception_successors.push(destination);
                    blocks[destination].exception_predecessors.push(source);
                }
            }
        }
        Ok(Self {
            blocks,
            block_offsets,
        })
    }

    /// Resolves a block's starting bytecode offset, not an arbitrary offset within it.
    pub fn block_at(&self, offset: u32) -> Option<usize> {
        self.block_offsets.binary_search(&offset).ok()
    }
}

#[cfg(test)]
mod tests;
