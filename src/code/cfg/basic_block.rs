// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! `code.cfg.BasicBlock`: a straight-line run of instructions and its
//! neighbours in the control-flow graph.

use std::sync::Arc;

use crate::code::{Instruction, InstructionSequence};
use crate::decompiler::ir::{BlockId, Ir};
use crate::engine::Cx;

#[derive(Default)]
pub struct BasicBlock {
    pub id: i32,
    pub mark: i32,
    pub seq: InstructionSequence,
    pub preds: Vec<BlockId>,
    pub succs: Vec<BlockId>,
    pub instr_old_offsets: Vec<i32>,
    pub pred_exceptions: Vec<BlockId>,
    pub succ_exceptions: Vec<BlockId>,
}

impl BasicBlock {
    /// `new BasicBlock(id)`.
    pub fn new(ir: &mut Ir, id: i32) -> BlockId {
        ir.blocks.push(BasicBlock {
            id,
            ..BasicBlock::default()
        })
    }

    pub fn get_instruction(&self, index: i32) -> &Arc<Instruction> {
        self.seq.get_instr(index)
    }

    pub fn get_last_instruction(&self) -> Option<&Arc<Instruction>> {
        (!self.seq.is_empty()).then(|| self.seq.get_last_instr())
    }

    pub fn get_old_offset(&self, index: i32) -> i32 {
        self.instr_old_offsets
            .get(index as usize)
            .copied()
            .unwrap_or(-1)
    }

    pub fn size(&self) -> i32 {
        self.seq.length()
    }

    pub fn get_start_instruction(&self) -> i32 {
        if self.seq.is_empty() {
            return 0;
        }
        self.instr_old_offsets[0]
    }

    pub fn get_end_instruction(&self) -> i32 {
        if self.seq.is_empty() {
            return 0;
        }
        let end = self.seq.get_last_instr().length;
        end + self.instr_old_offsets[self.size() as usize - 1]
    }
}

impl BlockId {
    pub fn add_predecessor(self, ir: &mut Ir, block: BlockId) {
        ir[self].preds.push(block);
    }

    pub fn remove_predecessor(self, ir: &mut Ir, block: BlockId) {
        ir[self].preds.retain(|&pred| pred != block);
    }

    pub fn add_successor(self, ir: &mut Ir, block: BlockId) {
        ir[self].succs.push(block);
        block.add_predecessor(ir, self);
    }

    pub fn remove_successor(self, ir: &mut Ir, block: BlockId) {
        ir[self].succs.retain(|&succ| succ != block);
        block.remove_predecessor(ir, self);
    }

    // FIXME: unify block comparisons: id or direct equality
    pub fn replace_successor(self, ir: &mut Ir, old_block: BlockId, new_block: BlockId) {
        if old_block == new_block {
            return;
        }

        let old_id = ir[old_block].id;
        for i in 0..ir[self].succs.len() {
            if ir[ir[self].succs[i]].id == old_id {
                ir[self].succs[i] = new_block;
                old_block.remove_predecessor(ir, self);
                new_block.add_predecessor(ir, self);
            }
        }

        for i in 0..ir[self].succ_exceptions.len() {
            if ir[ir[self].succ_exceptions[i]].id == old_id {
                ir[self].succ_exceptions[i] = new_block;
                old_block.remove_predecessor_exception(ir, self);
                new_block.add_predecessor_exception(ir, self);
            }
        }
    }

    pub fn add_predecessor_exception(self, ir: &mut Ir, block: BlockId) {
        ir[self].pred_exceptions.push(block);
    }

    pub fn remove_predecessor_exception(self, ir: &mut Ir, block: BlockId) {
        ir[self].pred_exceptions.retain(|&pred| pred != block);
    }

    pub fn add_successor_exception(self, ir: &mut Ir, block: BlockId) {
        if !ir[self].succ_exceptions.contains(&block) {
            ir[self].succ_exceptions.push(block);
            block.add_predecessor_exception(ir, self);
        }
    }

    pub fn remove_successor_exception(self, ir: &mut Ir, block: BlockId) {
        ir[self].succ_exceptions.retain(|&succ| succ != block);
        block.remove_predecessor_exception(ir, self);
    }

    /// `toString(indent)`.
    pub fn to_string(self, cx: &Cx, indent: i32) -> String {
        let block = &cx.ir[self];
        format!(
            "{}:{}{}",
            block.id,
            cx.options.line_separator(),
            block.seq.to_string_indent(cx, indent)
        )
    }

    pub fn is_successor(self, ir: &Ir, block: BlockId) -> bool {
        let id = ir[block].id;
        ir[self].succs.iter().any(|&succ| ir[succ].id == id)
    }

    /// A block with the same instructions and no neighbours.
    pub fn clone_block(self, ir: &mut Ir, id: i32) -> BlockId {
        let block = BasicBlock {
            id,
            seq: ir[self].seq.clone(),
            instr_old_offsets: ir[self].instr_old_offsets.clone(),
            ..BasicBlock::default()
        };
        ir.blocks.push(block)
    }

    /// `getPredecessors()`: the regular predecessors, then the exceptional ones.
    pub fn get_predecessors(self, ir: &Ir) -> Vec<BlockId> {
        let block = &ir[self];
        block
            .preds
            .iter()
            .chain(&block.pred_exceptions)
            .copied()
            .collect()
    }
}
