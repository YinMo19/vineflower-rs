// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! The subroutine inlining phase of `code.cfg.ControlFlowGraph`.

use std::collections::VecDeque;

use indexmap::IndexSet;
use rustc_hash::FxHashMap;

use super::{ControlFlowGraph, ExceptionRangeCFG};
use crate::code::code_constants::{OPC_ASTORE, OPC_JSR, OPC_POP, OPC_RET};
use crate::code::{dead_code_helper, interpreter};
use crate::decompiler::ir::{BlockId, Ir};
use crate::engine::Options;
use crate::structs::{StructClass, StructMethod, consts::ConstantPool};
use crate::types::{CodeType, data_point::DataPoint};

struct JsrRange {
    enter: BlockId,
    ret: BlockId,
    blocks: IndexSet<BlockId>,
}

impl ControlFlowGraph {
    pub fn inline_jsr(
        &mut self,
        ir: &mut Ir,
        class: &StructClass,
        method: &StructMethod,
        options: &Options,
    ) {
        while let Some((enter, ret, shared)) = self.intersecting_jsr_ranges(ir) {
            self.split_jsr_range(ir, enter, ret, &shared);
        }
        self.remove_jsr_instructions(ir, &class.pool, DataPoint::initial(class, method));
        self.remove_markers(ir);
        dead_code_helper::remove_empty_blocks(ir, self, options);
    }

    fn intersecting_jsr_ranges(&self, ir: &Ir) -> Option<(BlockId, BlockId, IndexSet<BlockId>)> {
        let mut ranges: Vec<JsrRange> = Vec::with_capacity(self.subroutines.len());
        for (&enter, &ret) in &self.subroutines {
            let blocks = self.jsr_range(ir, enter, ret);
            let before = ranges
                .iter()
                .position(|r| r.blocks.contains(&enter))
                .unwrap_or(ranges.len());
            ranges.insert(before, JsrRange { enter, ret, blocks });
        }

        for (index, outer) in ranges.iter().enumerate() {
            for other in &ranges[index + 1..] {
                if outer.blocks.contains(&other.enter) || other.blocks.contains(&outer.enter) {
                    continue;
                }
                let shared: IndexSet<_> =
                    outer.blocks.intersection(&other.blocks).copied().collect();
                if !shared.is_empty() {
                    return Some((outer.enter, outer.ret, shared));
                }
            }
        }
        None
    }

    fn jsr_range(&self, ir: &Ir, enter: BlockId, ret: BlockId) -> IndexSet<BlockId> {
        let dom = ir[enter].succs[0];
        let mut blocks = IndexSet::new();
        let mut predecessor_dominance = FxHashMap::default();
        let mut queue = VecDeque::from([enter]);
        while let Some(node) = queue.pop_front() {
            let successors = subroutine_edges(ir, node, enter, ret, false)
                .iter()
                .rev()
                .chain(subroutine_edges(ir, node, enter, ret, true).iter().rev());
            for &child in successors {
                if blocks.contains(&child) {
                    continue;
                }
                if node != enter
                    && !ir[child]
                        .preds
                        .iter()
                        .chain(&ir[child].pred_exceptions)
                        .all(|&pred| {
                            *predecessor_dominance.entry(pred).or_insert_with(|| {
                                dead_code_helper::is_dominator(ir, self, pred, dom)
                            })
                        })
                {
                    continue;
                }
                if child != self.last {
                    blocks.insert(child);
                }
                queue.push_back(child);
            }
        }
        blocks
    }

    fn split_jsr_range(
        &mut self,
        ir: &mut Ir,
        enter: BlockId,
        ret: BlockId,
        shared: &IndexSet<BlockId>,
    ) {
        let mut copies = FxHashMap::default();
        copies.insert(ir[enter].id, enter);
        let mut queue = VecDeque::from([enter]);
        while let Some(node) = queue.pop_front() {
            for exceptional in [false, true] {
                let count = subroutine_edges(ir, node, enter, ret, exceptional).len();
                for i in (0..count).rev() {
                    // replaceSuccessor can redirect several occurrences in this same list.
                    let child = if exceptional {
                        ir[node].succ_exceptions[i]
                    } else {
                        ir[node].succs[i]
                    };
                    let id = ir[child].id;
                    if let Some(&copy) = copies.get(&id) {
                        node.replace_successor(ir, child, copy);
                    } else if shared.contains(&child) {
                        self.last_id += 1;
                        let copy = child.clone_block(ir, self.last_id);
                        if ir[child].seq.get_last_instr().opcode == OPC_RET
                            && ir[child].succs.contains(&ret)
                        {
                            copy.add_successor(ir, ret);
                            child.remove_successor(ir, ret);
                        } else {
                            for succ in ir[child].succs.clone() {
                                copy.add_successor(ir, succ);
                            }
                        }
                        for handler in ir[child].succ_exceptions.clone() {
                            copy.add_successor_exception(ir, handler);
                        }
                        if ir[self.last].preds.contains(&child) {
                            self.last.add_predecessor(ir, copy);
                        }
                        node.replace_successor(ir, child, copy);
                        self.blocks.add_with_key(copy, self.last_id);
                        copies.insert(id, copy);
                        queue.push_back(copy);
                    } else {
                        copies.insert(id, child);
                    }
                }
            }
        }

        for i in (0..self.exceptions.len()).rev() {
            let range = &self.exceptions[i];
            let overlap: Vec<_> = range
                .protected_range
                .iter()
                .copied()
                .filter(|block| shared.contains(block))
                .collect::<IndexSet<_>>()
                .into_iter()
                .map(|block| copies[&ir[block].id])
                .collect();
            if overlap.is_empty() {
                continue;
            }
            if overlap.len() == range.protected_range.len() {
                self.exceptions.push(ExceptionRangeCFG::new(
                    overlap,
                    copies[&ir[range.handler].id],
                    range.exception_types.clone(),
                ));
            } else {
                self.exceptions[i].protected_range.extend(overlap);
            }
        }
    }

    fn remove_jsr_instructions(&self, ir: &mut Ir, pool: &ConstantPool, initial: DataPoint) {
        let enter_block = |ir: &mut Ir, node: BlockId, mut frame: DataPoint| {
            ir[node].seq.retain(|inst| {
                let consumes_address = matches!(inst.opcode, OPC_ASTORE | OPC_POP)
                    && frame.stack().last().expect("empty operand stack").ty == CodeType::Address;
                interpreter::step_types(&mut frame, inst, pool);
                !consumes_address && !matches!(inst.opcode, OPC_JSR | OPC_RET)
            });
            ir[node].mark = 1;
            (node, frame, 0)
        };

        if ir[self.first].mark == 1 {
            return;
        }
        // Follow each regular edge before the exceptional edges of the same
        // block. Only the first visit to a successor needs a copy of the frame.
        let mut stack = vec![enter_block(ir, self.first, initial)];
        while let Some((node, frame, next_edge)) = stack.last_mut() {
            let block = &ir[*node];
            let exceptional = *next_edge >= block.succs.len();
            let successor = if exceptional {
                block.succ_exceptions.get(*next_edge - block.succs.len())
            } else {
                block.succs.get(*next_edge)
            };
            let Some(&successor) = successor else {
                stack.pop();
                continue;
            };
            *next_edge += 1;
            if ir[successor].mark == 1 {
                continue;
            }

            let next_frame = if exceptional {
                frame.exception_successor()
            } else {
                frame.clone()
            };
            if *next_edge == block.succs.len() + block.succ_exceptions.len() {
                stack.pop();
            }
            stack.push(enter_block(ir, successor, next_frame));
        }
    }
}

fn subroutine_edges(
    ir: &Ir,
    node: BlockId,
    enter: BlockId,
    ret: BlockId,
    exceptional: bool,
) -> &[BlockId] {
    let block = &ir[node];
    if exceptional {
        if node == enter {
            &[]
        } else {
            &block.succ_exceptions
        }
    } else if block.seq.get_last_instr().opcode == OPC_RET && block.succs.contains(&ret) {
        &[]
    } else {
        &block.succs
    }
}
