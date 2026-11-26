// Copyright 2000-2024 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Match each normal exit from a protected region against its finally handler.

use std::collections::VecDeque;
use std::io;
use std::sync::Arc;

use indexmap::{IndexMap, IndexSet};

use crate::code::cfg::ControlFlowGraph;
use crate::code::code_constants::{
    GROUP_JUMP, GROUP_SWITCH, OPC_ALOAD, OPC_ASTORE, OPC_IINC, OPC_ILOAD, OPC_SASTORE,
};
use crate::code::{Instruction, dead_code_helper};
use crate::decompiler::ir::{BlockId, Ir, StatId};
use crate::decompiler::sforms::InstructionRewrites;
use crate::decompiler::stats::StatementKind;
use crate::decompiler::vars::version_graph::VarVersionsGraph;
use crate::engine::method_timeout::checkpoint;
use crate::util::interpreter_util::equal_sets;

use super::rewrite::{delete_area, remove_exception_instructions};
use super::{FinallyInfo, HandlerKind, basic_blocks, basic_head};

/// `FinallyProcessor.verifyFinallyEx`. Sample dissection changes the live
/// graph even if a later comparison fails.
pub(super) fn verify(
    ir: &mut Ir,
    graph: &mut ControlFlowGraph,
    stat: StatId,
    info: &FinallyInfo,
    rewrites: &InstructionRewrites,
    versions: &VarVersionsGraph,
) -> io::Result<bool> {
    let StatementKind::CatchAll { handler, .. } = ir[stat].kind else {
        unreachable!("Finally verification requires a catch-all statement");
    };
    let handler = handler.expect("Missing catch-all handler");
    let try_blocks = basic_blocks(ir, ir[stat].first.expect("Missing try body"));
    let catch_blocks = basic_blocks(ir, handler);
    let handler_head = basic_head(ir, handler);
    let kind = info.first_code;

    if kind == HandlerKind::Empty {
        remove_exception_instructions(ir, handler_head, true, true, kind)?;
        if info.last.contains_key(&handler_head) {
            graph.finally_exits.insert(handler_head);
        }
        return Ok(true);
    }

    let skipped_head = if ir[handler_head].size() == 1 && kind != HandlerKind::Stack {
        let successor = ir[handler_head].succs[0];
        catch_blocks.contains(&successor).then_some(successor)
    } else {
        None
    };

    let starts: IndexSet<_> = try_blocks
        .iter()
        .flat_map(|&block| ir[block].succs.iter().copied())
        .filter(|block| *block != graph.last && !try_blocks.contains(block))
        .collect();
    let comparison = Comparison {
        catch_blocks: &catch_blocks,
        start_catch: skipped_head.unwrap_or(handler_head),
        skipped_first: skipped_head.is_some(),
        info,
        rewrites,
        versions,
    };
    let mut areas = Vec::with_capacity(starts.len());
    for start in starts {
        let Some(area) = comparison.compare_subgraphs(ir, graph, start) else {
            return Ok(false);
        };
        areas.push(area);
    }
    for area in areas {
        delete_area(ir, graph, area.start, &area.sample, area.next);
    }

    for (&last, &is_true_exit) in &info.last {
        if is_true_exit {
            remove_exception_instructions(ir, last, false, true, kind)?;
            graph.finally_exits.insert(last);
        }
    }
    remove_exception_instructions(ir, handler_head, true, false, kind)?;
    Ok(true)
}

struct Area {
    start: BlockId,
    sample: IndexSet<BlockId>,
    next: Option<BlockId>,
}

struct BlockPair {
    catch: BlockId,
    sample: BlockId,
    /// Local reference slots matched along this path.
    store_vars: Vec<(i32, i32)>,
}

struct Exit {
    source: BlockId,
    target: BlockId,
    true_exit: bool,
}

struct Comparison<'a> {
    catch_blocks: &'a IndexSet<BlockId>,
    start_catch: BlockId,
    skipped_first: bool,
    info: &'a FinallyInfo,
    rewrites: &'a InstructionRewrites,
    versions: &'a VarVersionsGraph,
}

impl Comparison<'_> {
    fn compare_subgraphs(
        &self,
        ir: &mut Ir,
        graph: &mut ControlFlowGraph,
        start: BlockId,
    ) -> Option<Area> {
        let mut pending = VecDeque::from([BlockPair {
            catch: self.start_catch,
            sample: start,
            store_vars: Vec::new(),
        }]);
        // Preserve pairing order when deleting samples. Java's set uses
        // object identity, so its deletion order can differ.
        let mut samples = IndexSet::new();
        let mut exits = IndexMap::new();

        while let Some(BlockPair {
            catch,
            sample,
            mut store_vars,
        }) = pending.pop_front()
        {
            checkpoint();
            let last = self.info.last.get(&catch).copied();
            if !self.compare_basic_blocks(
                ir,
                graph,
                catch,
                sample,
                last == Some(true),
                &mut store_vars,
            ) || ir[sample].succs.len() != ir[catch].succs.len()
            {
                return None;
            }
            samples.insert(sample);

            for (&catch, &sample) in ir[catch].succs.iter().zip(&ir[sample].succs) {
                if self.catch_blocks.contains(&catch) && !samples.contains(&sample) {
                    pending.push_back(BlockPair {
                        catch,
                        sample,
                        store_vars: store_vars.clone(),
                    });
                }
            }

            // An empty sample exit will be removed, so its protection is immaterial.
            if last.is_none() || !ir[sample].seq.is_empty() {
                if ir[catch].succ_exceptions.len() != ir[sample].succ_exceptions.len() {
                    return None;
                }
                for (&catch_handler, &sample_handler) in ir[catch]
                    .succ_exceptions
                    .iter()
                    .zip(&ir[sample].succ_exceptions)
                {
                    let catch_types = graph
                        .get_exception_range(catch_handler, catch)
                        .expect("Missing exception range for handler")
                        .get_unique_exceptions_string();
                    let sample_types = graph
                        .get_exception_range(sample_handler, sample)
                        .expect("Missing exception range for sample")
                        .get_unique_exceptions_string();
                    if catch_types != sample_types {
                        return None;
                    }
                    if self.catch_blocks.contains(&catch_handler)
                        && !samples.contains(&sample_handler)
                    {
                        let mut handler_stores = store_vars.clone();
                        if let (Some(catch_store), Some(sample_store)) = (
                            ir[catch_handler].seq.iter().next(),
                            ir[sample_handler].seq.iter().next(),
                        ) && catch_store.opcode == OPC_ASTORE
                            && sample_store.opcode == OPC_ASTORE
                        {
                            handler_stores.push((catch_store.operand(0), sample_store.operand(0)));
                        }
                        pending.push_back(BlockPair {
                            catch: catch_handler,
                            sample: sample_handler,
                            store_vars: handler_stores,
                        });
                    }
                }
            }

            if let Some(true_exit) = last {
                for &target in &ir[sample].succs {
                    if target != graph.last
                        && !samples.contains(&target)
                        && !pending.iter().any(|pair| pair.sample == target)
                    {
                        exits.insert(
                            (ir[sample].id, ir[target].id),
                            Exit {
                                source: sample,
                                target,
                                true_exit,
                            },
                        );
                    }
                }
            }
        }

        Some(Area {
            start,
            sample: samples,
            next: unique_next(ir, graph, &exits),
        })
    }

    fn compare_basic_blocks(
        &self,
        ir: &mut Ir,
        graph: &mut ControlFlowGraph,
        pattern: BlockId,
        sample: BlockId,
        true_last: bool,
        store_vars: &mut Vec<(i32, i32)>,
    ) -> bool {
        let kind = self.info.first_code;
        let first = i32::from(
            !self.skipped_first && pattern == self.start_catch && kind != HandlerKind::Stack,
        );
        let tail = if true_last {
            match kind {
                HandlerKind::Stack => 1,
                HandlerKind::Store => 2,
                HandlerKind::Pop | HandlerKind::Empty => 0,
            }
        } else {
            0
        };
        let end = ir[pattern].size() - tail;
        assert!(first <= end, "Finally bookkeeping exceeds pattern length");
        let pattern_size = end - first;
        if pattern_size > ir[sample].size() {
            return false;
        }
        for (pattern_index, sample_index) in (first..end).zip(0..) {
            if !self.equal_instructions(
                ir[pattern].get_instruction(pattern_index),
                ir[sample].get_instruction(sample_index),
                store_vars,
            ) {
                return false;
            }
        }
        if pattern_size < ir[sample].size() {
            split_sample(ir, graph, sample, pattern_size);
        }
        true
    }

    fn equal_instructions(
        &self,
        first: &Arc<Instruction>,
        second: &Arc<Instruction>,
        store_vars: &mut Vec<(i32, i32)>,
    ) -> bool {
        if !Instruction::equals(first, second) {
            return false;
        }
        if matches!(first.group, GROUP_JUMP | GROUP_SWITCH) {
            return true;
        }
        for index in 0..first.operands_count() {
            let left = first.operand(index);
            let right = second.operand(index);
            if left == right {
                continue;
            }
            if first.opcode == OPC_ALOAD && store_vars.contains(&(left, right)) {
                return true;
            }
            if first.opcode == OPC_ASTORE {
                store_vars.push((left, right));
                return true;
            }
            if !matches!(first.opcode, OPC_ILOAD..=OPC_SASTORE | OPC_IINC)
                || !self.versions.are_vars_analogous(
                    self.rewrites.get(first).unwrap_or(left),
                    self.rewrites.get(second).unwrap_or(right),
                )
            {
                return false;
            }
        }
        true
    }
}

fn get_side_exits<'a>(exits: impl Iterator<Item = &'a Exit>) -> IndexSet<BlockId> {
    exits
        .filter(|exit| !exit.true_exit)
        .map(|exit| exit.target)
        .collect()
}

fn unique_next(
    ir: &mut Ir,
    graph: &mut ControlFlowGraph,
    exits: &IndexMap<(i32, i32), Exit>,
) -> Option<BlockId> {
    // The verifier expects at most one true exit. When several appear, pairing
    // order selects the first, where Java uses the array objects' hash order.
    if let Some(exit) = exits.values().find(|exit| exit.true_exit) {
        return Some(exit.target);
    }
    // In the absence of a true exit, prefer the last single-predecessor exit,
    // or the first discovered exit otherwise. Java iterates an identity hash
    // set here, so tied equivalent exits can leave a different block ID alive.
    let next = exits
        .values()
        .rev()
        .find(|exit| ir[exit.target].preds.len() == 1)
        .or_else(|| exits.values().next())?
        .target;
    let side_exits = get_side_exits(exits.values());
    if side_exits.len() > 1 {
        for other in side_exits {
            if other != next && !equivalent_continuation(ir, next, other) {
                return None;
            }
        }
        for exit in exits.values() {
            if exit.target != next {
                exit.source.remove_successor(ir, exit.target);
                exit.source.add_successor(ir, next);
            }
        }
        dead_code_helper::remove_dead_blocks(ir, graph);
    }
    Some(next)
}

fn equivalent_continuation(ir: &Ir, next: BlockId, other: BlockId) -> bool {
    let first = &ir[next];
    let second = &ir[other];
    equal_sets(&first.succs, &second.succs)
        && first.size() == second.size()
        && first
            .seq
            .iter()
            .zip(second.seq.iter())
            .all(|(left, right)| {
                Instruction::equals(left, right)
                    && (0..left.operands_count())
                        .all(|index| left.operand(index) == right.operand(index))
            })
}

fn split_sample(ir: &mut Ir, graph: &mut ControlFlowGraph, sample: BlockId, cut: i32) {
    let block = &mut ir[sample];
    let length = block.size() as usize;
    let cut = cut as usize;
    let tail = block.seq.split_off(cut);
    // Absent offsets read as -1; stale offsets beyond the instruction list
    // remain on the old block, as they do in compareBasicBlocksEx.
    let stored = block.instr_old_offsets.len();
    let mut offsets: Vec<_> = block
        .instr_old_offsets
        .drain(cut.min(stored)..length.min(stored))
        .collect();
    offsets.resize(length - cut, -1);

    let new = graph.new_block(ir);
    ir[new].seq = tail;
    ir[new].instr_old_offsets = offsets;
    for successor in ir[sample].succs.clone() {
        sample.remove_successor(ir, successor);
        new.add_successor(ir, successor);
    }
    sample.add_successor(ir, new);
    if graph.finally_exits.shift_remove(&sample) {
        graph.finally_exits.insert(new);
    }
    for handler in ir[sample].succ_exceptions.clone() {
        new.add_successor_exception(ir, handler);
        graph
            .get_exception_range_mut(handler, sample)
            .expect("Missing exception range of split sample")
            .protected_range
            .push(new);
    }
}
