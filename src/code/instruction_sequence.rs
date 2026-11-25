// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! `code.InstructionSequence` and `code.FullInstructionSequence`: the
//! instructions of a basic block, and those of a whole method together with
//! its offset index and exception table.

use std::fmt::Write as _;
use std::slice;
use std::sync::Arc;

use rustc_hash::FxHashMap;

use super::exception_table::ExceptionTable;
use super::instruction::Instruction;
use crate::engine::Cx;
use crate::util::text_util;

/// Cloning copies the list and shares its instructions, as upstream's
/// `clone()` does.
#[derive(Clone, Debug, Default)]
pub struct InstructionSequence {
    instructions: Vec<Arc<Instruction>>,
}

impl InstructionSequence {
    pub fn new() -> Self {
        Self::default()
    }

    /// `new InstructionSequence(instructions)`.
    pub fn from_collection(instructions: impl IntoIterator<Item = Arc<Instruction>>) -> Self {
        Self {
            instructions: instructions.into_iter().collect(),
        }
    }

    // *****************************************************************************
    // public methods
    // *****************************************************************************

    pub fn clear(&mut self) {
        self.instructions.clear();
    }

    pub fn add_instruction(&mut self, inst: Arc<Instruction>) {
        self.instructions.push(inst);
    }

    /// `addInstruction(index, inst)`.
    pub fn add_instruction_at(&mut self, index: i32, inst: Arc<Instruction>) {
        self.instructions.insert(index as usize, inst);
    }

    pub fn add_sequence(&mut self, seq: &InstructionSequence) {
        self.instructions.extend_from_slice(&seq.instructions);
    }

    pub fn remove_instruction(&mut self, index: i32) {
        self.instructions.remove(index as usize);
    }

    /// Move the suffix to another block, preserving the identity of its instructions.
    pub(crate) fn split_off(&mut self, index: usize) -> Self {
        Self {
            instructions: self.instructions.split_off(index),
        }
    }

    /// Visits instructions in execution order, retaining those selected by the pass.
    pub(crate) fn retain(&mut self, mut keep: impl FnMut(&Instruction) -> bool) {
        self.instructions.retain(|instruction| keep(instruction));
    }

    pub fn remove_last(&mut self) {
        self.instructions.pop();
    }

    pub fn get_instr(&self, index: i32) -> &Arc<Instruction> {
        &self.instructions[index as usize]
    }

    pub fn get_last_instr(&self) -> &Arc<Instruction> {
        &self.instructions[self.instructions.len() - 1]
    }

    pub fn length(&self) -> i32 {
        self.instructions.len() as i32
    }

    pub fn is_empty(&self) -> bool {
        self.instructions.is_empty()
    }

    pub fn to_string(&self, cx: &Cx) -> String {
        self.to_string_indent(cx, 0)
    }

    /// `toString(indent)`.
    pub fn to_string_indent(&self, cx: &Cx, indent: i32) -> String {
        instructions_to_string(cx, &self.instructions, indent)
    }

    // *****************************************************************************
    // getter and setter methods
    // *****************************************************************************

    pub fn iter(&self) -> slice::Iter<'_, Arc<Instruction>> {
        self.instructions.iter()
    }
}

impl<'a> IntoIterator for &'a InstructionSequence {
    type Item = &'a Arc<Instruction>;
    type IntoIter = slice::Iter<'a, Arc<Instruction>>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

#[derive(Debug)]
pub struct FullInstructionSequence {
    pub instructions: Vec<Arc<Instruction>>,
    /// The index in `instructions` of the instruction at each bytecode offset.
    pub offset_to_index: FxHashMap<i32, i32>,
    pub exception_table: ExceptionTable,
}

impl FullInstructionSequence {
    pub fn get_instr(&self, index: i32) -> &Arc<Instruction> {
        &self.instructions[index as usize]
    }

    pub fn length(&self) -> i32 {
        self.instructions.len() as i32
    }

    pub fn is_empty(&self) -> bool {
        self.instructions.is_empty()
    }

    /// The index of the instruction `offset` bytes after the start of
    /// `instruction`, or -1 if no instruction starts there.
    pub fn get_index_by_rel_offset(&self, instruction: &Instruction, offset: i32) -> i32 {
        let absolute_offset = instruction.start_offset.wrapping_add(offset);
        self.offset_to_index
            .get(&absolute_offset)
            .copied()
            .unwrap_or(-1)
    }

    pub fn iter(&self) -> slice::Iter<'_, Arc<Instruction>> {
        self.instructions.iter()
    }

    pub fn to_string(&self, cx: &Cx) -> String {
        self.to_string_indent(cx, 0)
    }

    /// `toString(indent)`.
    pub fn to_string_indent(&self, cx: &Cx, indent: i32) -> String {
        instructions_to_string(cx, &self.instructions, indent)
    }

    pub fn get_last(&self) -> &Arc<Instruction> {
        &self.instructions[self.instructions.len() - 1]
    }
}

impl<'a> IntoIterator for &'a FullInstructionSequence {
    type Item = &'a Arc<Instruction>;
    type IntoIter = slice::Iter<'a, Arc<Instruction>>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// `toString(indent)` of both sequences: one line per instruction.
fn instructions_to_string(cx: &Cx, instructions: &[Arc<Instruction>], indent: i32) -> String {
    let new_line_separator = cx.options.line_separator();

    let mut buf = String::new();

    for instr in instructions {
        buf.push_str(&text_util::get_indent_string(cx, indent));
        write!(buf, "{}: {instr}", instr.start_offset).unwrap();
        buf.push_str(new_line_separator);
    }

    buf
}
