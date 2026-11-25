// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! `code.Instruction` with its subclasses `JumpInstruction` and
//! `SwitchInstruction`: one decoded bytecode instruction.
//!
//! An instruction never changes once its sequence is built, and upstream
//! hands the same object to the method's sequence, to basic blocks and to the
//! expressions decompiled from it, some of which key maps by its identity.
//! The port shares it as `Arc<Instruction>`: cloning the `Arc` copies the
//! Java reference and `Arc::ptr_eq` is `==`, whereas upstream's `clone()` is
//! [`Instruction::clone`] placed in an `Arc` of its own.

use std::fmt;

use super::bytecode_version::BytecodeVersion;
use super::code_constants::{
    OPC_ATHROW, OPC_GOTO, OPC_GOTO_W, OPC_IF_ACMPNE, OPC_IFEQ, OPC_IFNONNULL, OPC_IFNULL,
    OPC_IRETURN, OPC_JSR, OPC_JSR_W, OPC_LOOKUPSWITCH, OPC_RET, OPC_RETURN, OPC_TABLESWITCH,
};
use super::instruction_sequence::FullInstructionSequence;
use crate::util::text_util;

#[derive(Clone, Debug)]
pub struct Instruction {
    pub opcode: i32,
    pub group: i32,
    pub wide: bool,
    pub bytecode_version: BytecodeVersion,
    pub start_offset: i32,
    pub length: i32,
    /// Empty where upstream has `null`.
    operands: Vec<i32>,
    pub kind: InstructionKind,
}

/// The subclass of an instruction, with the fields that subclass adds.
#[derive(Clone, Debug)]
pub enum InstructionKind {
    /// An `Instruction` that is neither a jump nor a switch.
    Plain,
    Jump(JumpInstruction),
    Switch(SwitchInstruction),
}

#[derive(Clone, Debug, Default)]
pub struct JumpInstruction {
    /// The index of the target instruction, or -1 if nothing starts there.
    pub destination: i32,
}

/// Empty until `init_instruction` has run.
#[derive(Clone, Debug, Default)]
pub struct SwitchInstruction {
    /// The index of each case's target instruction, parallel to `values`.
    pub destinations: Vec<i32>,
    pub values: Vec<i32>,
    pub default_destination: i32,
}

impl Instruction {
    /// Pass no operands where upstream passes `null`.
    pub fn create(
        opcode: i32,
        wide: bool,
        group: i32,
        bytecode_version: BytecodeVersion,
        operands: Vec<i32>,
        start_offset: i32,
        length: i32,
    ) -> Instruction {
        let kind = if (OPC_IFEQ..=OPC_IF_ACMPNE).contains(&opcode)
            || opcode == OPC_IFNULL
            || opcode == OPC_IFNONNULL
            || opcode == OPC_JSR
            || opcode == OPC_JSR_W
            || opcode == OPC_GOTO
            || opcode == OPC_GOTO_W
        {
            InstructionKind::Jump(JumpInstruction::default())
        } else if opcode == OPC_TABLESWITCH || opcode == OPC_LOOKUPSWITCH {
            InstructionKind::Switch(SwitchInstruction::default())
        } else {
            InstructionKind::Plain
        };

        Instruction {
            opcode,
            group,
            wide,
            bytecode_version,
            start_offset,
            length,
            operands,
            kind,
        }
    }

    /// Whether two instructions are the same operation, whatever their operands.
    pub fn equals(i1: &Instruction, i2: &Instruction) -> bool {
        std::ptr::eq(i1, i2)
            || i1.opcode == i2.opcode
                && i1.wide == i2.wide
                && i1.operands_count() == i2.operands_count()
    }

    /// Resolves the relative offsets of a jump or switch to instruction
    /// indices of `seq`.
    pub fn init_instruction(&mut self, seq: &FullInstructionSequence) {
        self.kind = match self.kind {
            InstructionKind::Plain => return,
            InstructionKind::Jump(_) => InstructionKind::Jump(self.init_jump(seq)),
            InstructionKind::Switch(_) => InstructionKind::Switch(self.init_switch(seq)),
        };
    }

    fn init_jump(&self, seq: &FullInstructionSequence) -> JumpInstruction {
        JumpInstruction {
            destination: seq.get_index_by_rel_offset(self, self.operand(0)),
        }
    }

    fn init_switch(&self, seq: &FullInstructionSequence) -> SwitchInstruction {
        let default_destination = seq.get_index_by_rel_offset(self, self.operands[0]);

        let prefix = if self.opcode == OPC_TABLESWITCH { 3 } else { 2 };
        let mut len = self.operands.len() - prefix;
        let mut low = 0;
        if self.opcode == OPC_LOOKUPSWITCH {
            len /= 2;
        } else {
            low = self.operands[1];
        }

        let mut destinations = vec![0; len];
        let mut values = vec![0; len];
        let mut k = 0;
        for i in 0..len {
            if self.opcode == OPC_LOOKUPSWITCH {
                values[i] = self.operands[prefix + k];
                k += 1;
            } else {
                values[i] = low.wrapping_add(k as i32);
            }
            destinations[i] = seq.get_index_by_rel_offset(self, self.operands[prefix + k]);
            k += 1;
        }

        SwitchInstruction {
            destinations,
            values,
            default_destination,
        }
    }

    pub fn operands_count(&self) -> i32 {
        self.operands.len() as i32
    }

    pub fn operand(&self, index: i32) -> i32 {
        self.operands[index as usize]
    }

    pub fn can_fall_through(&self) -> bool {
        self.opcode != OPC_GOTO
            && self.opcode != OPC_GOTO_W
            && self.opcode != OPC_RET
            && !(OPC_IRETURN..=OPC_RETURN).contains(&self.opcode)
            && self.opcode != OPC_ATHROW
            && self.opcode != OPC_JSR
            && self.opcode != OPC_TABLESWITCH
            && self.opcode != OPC_LOOKUPSWITCH
    }

    /// `(JumpInstruction) instr`.
    pub fn as_jump(&self) -> &JumpInstruction {
        match &self.kind {
            InstructionKind::Jump(jump) => jump,
            _ => panic!("Instruction cannot be cast to JumpInstruction"),
        }
    }

    /// `(SwitchInstruction) instr`.
    pub fn as_switch(&self) -> &SwitchInstruction {
        match &self.kind {
            InstructionKind::Switch(switch) => switch,
            _ => panic!("Instruction cannot be cast to SwitchInstruction"),
        }
    }
}

impl fmt::Display for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.wide {
            f.write_str("@wide ")?;
        }
        write!(f, "@{}", text_util::get_instruction_name(self.opcode))?;

        for &op in &self.operands {
            if op < 0 {
                write!(f, " -{:x}", op.wrapping_neg())?;
            } else {
                write!(f, " {op:x}")?;
            }
        }

        Ok(())
    }
}
