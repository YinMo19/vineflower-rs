// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! `code.cfg.ControlFlowGraph`: the method's basic blocks and their edges.

use std::collections::{VecDeque, hash_map::Entry};
use std::iter;

use indexmap::{IndexMap, IndexSet};
use itertools::Itertools;
use rustc_hash::{FxHashMap, FxHashSet};

use super::basic_block::BasicBlock;
use super::exception_range_cfg::ExceptionRangeCFG;
use crate::code::code_constants::{
    GROUP_FIELDACCESS, GROUP_GENERAL, GROUP_INVOCATION, GROUP_JUMP, GROUP_RETURN, GROUP_SWITCH,
    OPC_JSR, OPC_RET,
};
use crate::code::{FullInstructionSequence, InstructionSequence};
use crate::decompiler::ir::{BlockId, Ir};
use crate::engine::method_timeout::checkpoint;
use crate::util::vb_style_collection::VBStyleCollection;

pub struct ControlFlowGraph {
    pub blocks: VBStyleCollection<BlockId, i32>,
    pub first: BlockId,
    pub last: BlockId,
    pub last_id: i32,
    pub exceptions: Vec<ExceptionRangeCFG>,
    pub subroutines: IndexMap<BlockId, BlockId>,
    pub finally_exits: IndexSet<BlockId>,
    pub sequence: FullInstructionSequence,
    pub comment_lines: IndexSet<String>,
    pub add_error_comment: bool,
}

impl ControlFlowGraph {
    pub fn new(ir: &mut Ir, sequence: FullInstructionSequence) -> Self {
        let starts = Self::find_start_instructions(&sequence);
        let (blocks, instruction_blocks) = Self::create_basic_blocks(ir, &sequence, &starts);
        let first = blocks[0];
        let last = instruction_blocks[sequence.instructions.len()];
        let mut graph = Self {
            blocks,
            first,
            last,
            last_id: ir[last].id,
            exceptions: Vec::new(),
            subroutines: IndexMap::new(),
            finally_exits: IndexSet::new(),
            sequence,
            comment_lines: IndexSet::new(),
            add_error_comment: false,
        };

        graph.connect_blocks(ir, &instruction_blocks);
        graph.set_exception_edges(ir, &instruction_blocks);
        graph.set_subroutine_edges(ir);
        graph
    }

    fn find_start_instructions(sequence: &FullInstructionSequence) -> Vec<bool> {
        let mut starts = vec![false; sequence.instructions.len()];
        starts[0] = true;

        for handler in &sequence.exception_table.handlers {
            starts[handler.from as usize] = true;
            starts[handler.handler as usize] = true;
            if handler.to < sequence.length() {
                starts[handler.to as usize] = true;
            }
        }

        for (index, instruction) in sequence.iter().enumerate() {
            match instruction.group {
                GROUP_JUMP => starts[instruction.as_jump().destination as usize] = true,
                GROUP_SWITCH => {
                    let switch = instruction.as_switch();
                    starts[switch.default_destination as usize] = true;
                    for &destination in &switch.destinations {
                        starts[destination as usize] = true;
                    }
                }
                GROUP_RETURN => {}
                _ => continue,
            }

            if index + 1 < starts.len() {
                starts[index + 1] = true;
            }
        }
        starts
    }

    fn create_basic_blocks(
        ir: &mut Ir,
        sequence: &FullInstructionSequence,
        starts: &[bool],
    ) -> (VBStyleCollection<BlockId, i32>, Vec<BlockId>) {
        let boundaries = starts
            .iter()
            .enumerate()
            .filter_map(|(index, &start)| start.then_some(index))
            .chain(iter::once(starts.len()));
        let mut blocks = VBStyleCollection::new();
        let mut instruction_blocks = Vec::with_capacity(starts.len() + 1);

        for (start, end) in boundaries.tuple_windows() {
            let instructions = &sequence.instructions[start..end];
            // createBasicBlocks numbers the initial blocks with a Java short.
            let id = (blocks.len() + 1) as i16 as i32;
            let block = BasicBlock::new(ir, id);
            ir[block].seq = InstructionSequence::from_collection(instructions.iter().cloned());
            ir[block].instr_old_offsets = instructions
                .iter()
                .map(|instr| instr.start_offset)
                .collect();
            blocks.add_with_key(block, id);
            instruction_blocks.resize(end, block);
        }

        // Exception ranges can end at the virtual exit, which is outside `blocks`.
        instruction_blocks.push(BasicBlock::new(ir, (blocks.len() + 1) as i16 as i32));
        (blocks, instruction_blocks)
    }

    fn connect_blocks(&self, ir: &mut Ir, instruction_blocks: &[BlockId]) {
        for (index, &block) in self.blocks.iter().enumerate() {
            let instruction = ir[block].seq.get_last_instr().clone();
            let falls_through = match instruction.group {
                GROUP_JUMP => {
                    // The taken edge precedes the fall-through edge.
                    let destination = instruction.as_jump().destination as usize;
                    block.add_successor(ir, instruction_blocks[destination]);
                    instruction.can_fall_through()
                }
                GROUP_SWITCH => {
                    let switch = instruction.as_switch();
                    let destinations =
                        iter::once(&switch.default_destination).chain(&switch.destinations);
                    for &destination in destinations {
                        block.add_successor(ir, instruction_blocks[destination as usize]);
                    }
                    false
                }
                GROUP_RETURN => {
                    if instruction.opcode != OPC_RET {
                        self.last.add_predecessor(ir, block);
                    }
                    false
                }
                GROUP_GENERAL | GROUP_INVOCATION | GROUP_FIELDACCESS => true,
                _ => panic!("Unknown instruction group"),
            };

            if falls_through && let Some(&next) = self.blocks.get(index + 1) {
                block.add_successor(ir, next);
            }
        }
    }

    fn set_exception_edges(&mut self, ir: &mut Ir, instruction_blocks: &[BlockId]) {
        let mut ranges: FxHashMap<_, usize> = FxHashMap::default();
        for handler in &self.sequence.exception_table.handlers {
            checkpoint();
            let from = instruction_blocks[handler.from as usize];
            let to = instruction_blocks[handler.to as usize];
            let target = instruction_blocks[handler.handler as usize];
            let exception_type = handler.exception_class.clone();

            match ranges.entry((from, to, target)) {
                Entry::Occupied(entry) => {
                    self.exceptions[*entry.get()].add_exception_type(exception_type);
                }
                Entry::Vacant(entry) => {
                    let protected_range: Vec<_> = (ir[from].id..ir[to].id)
                        .map(|id| {
                            *self
                                .blocks
                                .get_with_key(&id)
                                .expect("missing protected block")
                        })
                        .collect();
                    for &block in &protected_range {
                        block.add_successor_exception(ir, target);
                    }

                    entry.insert(self.exceptions.len());
                    self.exceptions.push(ExceptionRangeCFG::new(
                        protected_range,
                        target,
                        exception_type.map(|class| vec![class]),
                    ));
                }
            }
        }
    }

    fn set_subroutine_edges(&mut self, ir: &mut Ir) {
        for &block in &self.blocks {
            if ir[block].seq.get_last_instr().opcode != OPC_JSR {
                continue;
            }

            let mut pending = VecDeque::from([(block, Vec::new())]);
            let mut visited = FxHashSet::default();

            while let Some((node, mut calls)) = pending.pop_front() {
                checkpoint();
                visited.insert(node);

                match ir[node].seq.get_last_instr().opcode {
                    OPC_JSR => calls.push(node),
                    OPC_RET => {
                        let enter = calls.pop().expect("ret requires a jsr call");
                        let &exit = self
                            .blocks
                            .get_with_key(&(ir[enter].id + 1))
                            .expect("ERROR: last instruction jsr");
                        if !node.is_successor(ir, exit) {
                            node.add_successor(ir, exit);
                        }
                        self.subroutines.insert(enter, exit);
                    }
                    _ => {}
                }

                if !calls.is_empty() {
                    pending.extend(
                        ir[node]
                            .succs
                            .iter()
                            .filter(|&successor| !visited.contains(successor))
                            .map(|&successor| (successor, calls.clone())),
                    );
                }
            }
        }
    }
}

impl ControlFlowGraph {
    pub fn new_block(&mut self, ir: &mut Ir) -> BlockId {
        self.last_id += 1;
        let block = BasicBlock::new(ir, self.last_id);
        self.blocks.add_with_key(block, self.last_id);
        block
    }

    pub fn add_comment(&mut self, comment: impl Into<String>) {
        self.comment_lines.insert(comment.into());
    }

    pub fn remove_markers(&self, ir: &mut Ir) {
        for &block in &self.blocks {
            ir[block].mark = 0;
        }
    }

    pub fn remove_block(&mut self, ir: &mut Ir, block: BlockId) {
        self.remove_block_tracking_ranges(ir, block, |_| {});
    }

    /// Reports removed ranges in increasing order of their pre-removal positions.
    pub(crate) fn remove_block_tracking_ranges(
        &mut self,
        ir: &mut Ir,
        block: BlockId,
        mut range_removed: impl FnMut(usize),
    ) {
        while let Some(&succ) = ir[block].succs.last() {
            block.remove_successor(ir, succ);
        }
        while let Some(&handler) = ir[block].succ_exceptions.last() {
            block.remove_successor_exception(ir, handler);
        }
        while let Some(&pred) = ir[block].preds.last() {
            pred.remove_successor(ir, block);
        }
        while let Some(&pred) = ir[block].pred_exceptions.last() {
            pred.remove_successor_exception(ir, block);
        }
        self.last.remove_predecessor(ir, block);
        self.blocks.remove_with_key(&ir[block].id);
        let mut index = 0;
        self.exceptions.retain_mut(|range| {
            let position = index;
            index += 1;
            let keep = if range.handler == block {
                false
            } else {
                if let Some(i) = range
                    .protected_range
                    .iter()
                    .position(|&member| member == block)
                {
                    range.protected_range.remove(i);
                }
                !range.protected_range.is_empty()
            };
            if !keep {
                range_removed(position);
            }
            keep
        });
        self.subroutines
            .retain(|&entry, exit| entry != block && *exit != block);
    }

    /// The last matching exception table entry takes precedence.
    pub fn get_exception_range(
        &self,
        handler: BlockId,
        block: BlockId,
    ) -> Option<&ExceptionRangeCFG> {
        let index = self.get_exception_range_index(handler, block)?;
        Some(&self.exceptions[index])
    }

    pub fn get_exception_range_mut(
        &mut self,
        handler: BlockId,
        block: BlockId,
    ) -> Option<&mut ExceptionRangeCFG> {
        let index = self.get_exception_range_index(handler, block)?;
        Some(&mut self.exceptions[index])
    }

    pub(crate) fn get_exception_range_index(
        &self,
        handler: BlockId,
        block: BlockId,
    ) -> Option<usize> {
        self.exceptions
            .iter()
            .rposition(|range| range.protects(handler, block))
    }

    pub fn get_reverse_post_order(&self, ir: &Ir) -> Vec<BlockId> {
        let mut visited = FxHashSet::default();
        let mut order = Vec::with_capacity(self.blocks.len());
        let mut stack = vec![(self.first, 0)];
        visited.insert(self.first);
        while let Some((node, index)) = stack.last_mut() {
            let block = &ir[*node];
            let next = if *index < block.succs.len() {
                block.succs.get(*index)
            } else {
                block.succ_exceptions.get(*index - block.succs.len())
            };
            match next {
                Some(&successor) => {
                    *index += 1;
                    if visited.insert(successor) {
                        stack.push((successor, 0));
                    }
                }
                None => order.push(stack.pop().unwrap().0),
            }
        }
        order.reverse();
        order
    }
}
