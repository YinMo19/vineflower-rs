// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! `modules.code.DeadCodeHelper`: cleanup and normalization of a method CFG.

use std::collections::VecDeque;

use indexmap::IndexSet;
use rustc_hash::FxHashSet;

use crate::code::cfg::ControlFlowGraph;
use crate::code::code_constants::{
    GROUP_SWITCH, OPC_ACONST_NULL, OPC_ALOAD, OPC_ATHROW, OPC_BIPUSH, OPC_DCONST_0, OPC_DCONST_1,
    OPC_DLOAD, OPC_FCONST_0, OPC_FCONST_1, OPC_FCONST_2, OPC_FLOAD, OPC_GOTO, OPC_ILOAD,
    OPC_IRETURN, OPC_LCONST_0, OPC_LCONST_1, OPC_LDC, OPC_LDC_W, OPC_LDC2_W, OPC_LLOAD,
    OPC_MONITORENTER, OPC_MONITOREXIT, OPC_RETURN, OPC_SIPUSH,
};
use crate::decompiler::ir::{BlockId, Ir};
use crate::engine::method_timeout::checkpoint;
use crate::engine::Options;

pub fn remove_dead_blocks(ir: &mut Ir, graph: &mut ControlFlowGraph) {
    let mut queue = VecDeque::from([graph.first]);
    let mut reachable = FxHashSet::default();
    reachable.insert(graph.first);

    while let Some(block) = queue.pop_front() {
        for &successor in ir[block].succs.iter().chain(&ir[block].succ_exceptions) {
            if reachable.insert(successor) {
                queue.push_back(successor);
            }
        }
    }

    let dead: Vec<_> = graph
        .blocks
        .iter()
        .copied()
        .filter(|block| !reachable.contains(block))
        .collect();
    for block in dead {
        graph.remove_block(ir, block);
    }
}

pub fn remove_empty_blocks(ir: &mut Ir, graph: &mut ControlFlowGraph, options: &Options) {
    loop {
        let mut deleted_ranges = false;
        for index in (0..graph.blocks.len()).rev() {
            checkpoint();
            if remove_empty_block(ir, graph, graph.blocks[index], false, options) {
                deleted_ranges = true;
                break;
            }
        }
        if !deleted_ranges {
            break;
        }
    }
}

/// Returns whether removing the block deleted an exception range and may have
/// removed other blocks as a result.
fn remove_empty_block(
    ir: &mut Ir,
    graph: &mut ControlFlowGraph,
    block: BlockId,
    merging: bool,
    options: &Options,
) -> bool {
    if !ir[block].seq.is_empty() {
        return false;
    }
    if ir[block].succs.len() > 1 {
        assert!(
            ir[block].preds.len() <= 1,
            "empty block with multiple predecessors and successors found"
        );
        assert!(merging, "empty block with multiple successors found");
    }

    if !ir[block].pred_exceptions.is_empty() {
        return false;
    }
    if ir[graph.last].preds.contains(&block) {
        let &[predecessor] = ir[block].preds.as_slice() else {
            return false;
        };
        if ir[predecessor].succs.len() != 1 || ends_with_switch(ir, predecessor) {
            return false;
        }
    }

    let predecessors: IndexSet<_> = ir[block].preds.iter().copied().collect();
    let successors: IndexSet<_> = ir[block].succs.iter().copied().collect();
    let mut neighbours = predecessors.iter().chain(&successors).copied();
    if let Some(neighbour) = neighbours.next() {
        let mut common_handlers: FxHashSet<_> =
            ir[neighbour].succ_exceptions.iter().copied().collect();
        for neighbour in neighbours {
            common_handlers.retain(|handler| ir[neighbour].succ_exceptions.contains(handler));
        }
        if common_handlers
            .iter()
            .any(|handler| !ir[block].succ_exceptions.contains(handler))
        {
            return false;
        }
    }

    let mut deleted_ranges = false;
    for index in (0..graph.exceptions.len()).rev() {
        let range = &graph.exceptions[index];
        if range.protected_range.as_slice() == [block] {
            if !options.remove_empty_try_catch {
                return false;
            }
            block.remove_successor_exception(ir, range.handler);
            graph.exceptions.remove(index);
            deleted_ranges = true;
        }
    }

    if merging {
        let predecessor = ir[block].preds[0];
        predecessor.remove_successor(ir, block);
        for successor in ir[block].succs.clone() {
            block.remove_successor(ir, successor);
            predecessor.add_successor(ir, successor);
        }
    } else {
        for &predecessor in &predecessors {
            for &successor in &successors {
                predecessor.replace_successor(ir, block, successor);
            }
        }
    }

    if graph.finally_exits.shift_remove(&block) {
        graph.finally_exits.insert(
            *predecessors
                .first()
                .expect("empty finally exit must have a predecessor"),
        );
    }
    if graph.first == block {
        assert_eq!(successors.len(), 1, "multiple or no entry blocks");
        graph.first = successors[0];
    }

    graph.remove_block(ir, block);
    if deleted_ranges {
        remove_dead_blocks(ir, graph);
    }
    deleted_ranges
}

pub fn is_dominator(ir: &Ir, graph: &ControlFlowGraph, block: BlockId, dom: BlockId) -> bool {
    if block == dom {
        return true;
    }

    let mut queue = VecDeque::from([block]);
    let mut marked = FxHashSet::default();
    marked.insert(block);
    while let Some(node) = queue.pop_front() {
        if node == graph.first {
            return false;
        }
        for &predecessor in ir[node].preds.iter().chain(&ir[node].pred_exceptions) {
            if predecessor != dom && marked.insert(predecessor) {
                queue.push_back(predecessor);
            }
        }
    }
    true
}

/// Keeps the goto instructions in a circular chain and in any goto-only
/// prefix leading into the chain.
fn find_circular_jumps(ir: &Ir, graph: &ControlFlowGraph) -> FxHashSet<BlockId> {
    let mut circular = FxHashSet::default();
    let mut classified = FxHashSet::default();
    let mut path = FxHashSet::default();

    for &block in &graph.blocks {
        if classified.contains(&block) {
            continue;
        }
        let mut current = block;
        let reaches_cycle = loop {
            if classified.contains(&current) {
                break circular.contains(&current);
            }
            if !path.insert(current) {
                break true;
            }
            match (last_opcode(ir, current), ir[current].succs.as_slice()) {
                (Some(OPC_GOTO), &[next]) => current = next,
                _ => break false,
            }
        };
        if reaches_cycle {
            circular.extend(&path);
        }
        classified.extend(path.drain());
    }
    circular
}

pub fn connect_dummy_exit_block(ir: &mut Ir, graph: &mut ControlFlowGraph) {
    let exit = graph.last;
    let predecessors: IndexSet<_> = ir[exit].preds.iter().copied().collect();
    for block in predecessors {
        exit.remove_predecessor(ir, block);
        block.add_successor(ir, exit);
    }
}

pub fn remove_gotos(ir: &mut Ir, graph: &mut ControlFlowGraph, options: &Options) {
    let circular = find_circular_jumps(ir, graph);
    for &block in &graph.blocks {
        if last_opcode(ir, block) == Some(OPC_GOTO) && !circular.contains(&block) {
            ir[block].seq.remove_last();
        }
    }
    remove_empty_blocks(ir, graph, options);
}

pub fn extend_synchronized_range_to_monitorexit(ir: &mut Ir, graph: &mut ControlFlowGraph) {
    loop {
        let mut extended = false;
        for index in 0..graph.exceptions.len() {
            checkpoint();
            let range = &graph.exceptions[index];
            let predecessors = range_boundary(&range.protected_range, |block| &ir[block].preds);
            if predecessors.len() != 1 || last_opcode(ir, predecessors[0]) != Some(OPC_MONITORENTER)
            {
                continue;
            }

            let handler = range.handler;
            if range
                .protected_range
                .iter()
                .copied()
                .chain([handler])
                .any(|block| monitorexit_position(ir, block).is_some())
            {
                continue;
            }

            let successors = range_boundary(&range.protected_range, |block| &ir[block].succs);
            if successors.len() != 1 || monitorexit_position(ir, successors[0]).is_none() {
                continue;
            }
            let successor = successors[0];

            let &[handler_successor] = ir[handler].succs.as_slice() else {
                continue;
            };
            if last_opcode(ir, handler_successor) != Some(OPC_ATHROW) {
                continue;
            }
            let Some(handler_monitorexit) = monitorexit_position(ir, handler_successor) else {
                continue;
            };

            let range_exit = ir[successor].preds[0];
            let handlers = ir[range_exit].succ_exceptions.clone();
            // When a shared successor's first predecessor belongs to another range,
            // the same candidate may otherwise be selected forever. A repeat only
            // changes the result if it moves instructions or extends coverage.
            if handler_monitorexit == 0
                && handlers.iter().all(|&hd| {
                    ir[successor].succ_exceptions.contains(&hd)
                        && graph
                            .get_exception_range(hd, range_exit)
                            .expect("exception edge must have a protected range")
                            .protected_range
                            .contains(&successor)
                })
            {
                continue;
            }
            for hd in handlers {
                add_to_protected_range(ir, graph, hd, range_exit, successor);
            }

            for _ in 0..handler_monitorexit {
                let instruction = ir[handler_successor].seq.get_instr(0).clone();
                ir[handler].seq.add_instruction(instruction);
                ir[handler_successor].seq.remove_instruction(0);
            }

            graph.add_comment("$VF: Extended synchronized range to monitorexit");
            extended = true;
            break;
        }
        if !extended {
            break;
        }
    }

    for range in &mut graph.exceptions {
        if range
            .protected_range
            .iter()
            .any(|&block| ir[block].succ_exceptions.len() > 1)
        {
            continue;
        }

        let predecessors = range_boundary(&range.protected_range, |block| &ir[block].preds);
        if predecessors.len() != 1 || last_opcode(ir, predecessors[0]) != Some(OPC_MONITORENTER) {
            continue;
        }

        let successors = range_boundary(&range.protected_range, |block| &ir[block].succs);
        for successor in successors {
            if last_opcode(ir, successor) == Some(OPC_MONITOREXIT) {
                range.protected_range.push(successor);
                successor.add_successor_exception(ir, range.handler);
            }
        }
    }
}

fn range_boundary<'a>(
    protected_range: &[BlockId],
    neighbours: impl Fn(BlockId) -> &'a [BlockId],
) -> IndexSet<BlockId> {
    let protected: FxHashSet<_> = protected_range.iter().copied().collect();
    protected_range
        .iter()
        .flat_map(|&block| neighbours(block).iter().copied())
        .filter(|block| !protected.contains(block))
        .collect()
}

fn monitorexit_position(ir: &Ir, block: BlockId) -> Option<usize> {
    ir[block]
        .seq
        .iter()
        .position(|instruction| instruction.opcode == OPC_MONITOREXIT)
}

pub fn incorporate_value_returns(ir: &mut Ir, graph: &mut ControlFlowGraph) {
    for index in 0..graph.blocks.len() {
        let block = graph.blocks[index];
        if !is_simple_return(ir, block) || ir[block].preds.is_empty() {
            continue;
        }

        let predecessor = ir[block].preds[0];
        let mut common_handlers: IndexSet<_> =
            ir[predecessor].succ_exceptions.iter().copied().collect();
        let mut predecessor_handlers = FxHashSet::default();
        for &predecessor in &ir[block].preds {
            let handlers = &ir[predecessor].succ_exceptions;
            common_handlers.retain(|handler| handlers.contains(handler));
            predecessor_handlers.extend(handlers.iter().copied());
        }
        common_handlers.retain(|handler| !ir[block].succ_exceptions.contains(handler));

        for handler in common_handlers {
            add_to_protected_range(ir, graph, handler, predecessor, block);
        }
        for handler in ir[block].succ_exceptions.clone() {
            if !predecessor_handlers.contains(&handler) {
                remove_from_redundant_range(ir, graph, handler, block);
            }
        }

        if ir[block].preds.len() == 1
            && ir[block].pred_exceptions.is_empty()
            && ir[predecessor].succs.len() == 1
        {
            for handler in ir[predecessor].succ_exceptions.clone() {
                if !ir[block].succ_exceptions.contains(&handler) {
                    add_to_protected_range(ir, graph, handler, predecessor, block);
                }
            }
            for handler in ir[block].succ_exceptions.clone() {
                if !ir[predecessor].succ_exceptions.contains(&handler) {
                    remove_from_redundant_range(ir, graph, handler, block);
                }
            }
        }
    }
}

fn is_simple_return(ir: &Ir, block: BlockId) -> bool {
    let seq = &ir[block].seq;
    let Some(opcode) = last_opcode(ir, block) else {
        return false;
    };
    if !(OPC_IRETURN..=OPC_RETURN).contains(&opcode) {
        return false;
    }

    seq.length() == 1
        || (seq.length() == 2
            && opcode != OPC_RETURN
            && matches!(
                seq.get_instr(0).opcode,
                OPC_ILOAD
                    | OPC_LLOAD
                    | OPC_FLOAD
                    | OPC_DLOAD
                    | OPC_ALOAD
                    | OPC_ACONST_NULL
                    | OPC_BIPUSH
                    | OPC_SIPUSH
                    | OPC_LCONST_0
                    | OPC_LCONST_1
                    | OPC_FCONST_0
                    | OPC_FCONST_1
                    | OPC_FCONST_2
                    | OPC_DCONST_0
                    | OPC_DCONST_1
                    | OPC_LDC
                    | OPC_LDC_W
                    | OPC_LDC2_W
            ))
}

fn add_to_protected_range(
    ir: &mut Ir,
    graph: &mut ControlFlowGraph,
    handler: BlockId,
    source: BlockId,
    block: BlockId,
) {
    let range = graph
        .get_exception_range_mut(handler, source)
        .expect("exception edge must have a protected range");
    range.protected_range.push(block);
    block.add_successor_exception(ir, handler);
}

fn remove_from_redundant_range(
    ir: &mut Ir,
    graph: &mut ControlFlowGraph,
    handler: BlockId,
    block: BlockId,
) {
    let range = graph
        .get_exception_range_mut(handler, block)
        .expect("exception edge must have a protected range");
    if range.protected_range.len() > 1 {
        let index = range
            .protected_range
            .iter()
            .position(|&protected| protected == block)
            .unwrap();
        range.protected_range.remove(index);
        block.remove_successor_exception(ir, handler);
    }
}

pub fn merge_basic_blocks(ir: &mut Ir, graph: &mut ControlFlowGraph, options: &Options) {
    loop {
        let origin_block_count = graph.blocks.len();
        for index in 0..origin_block_count {
            checkpoint();
            let block = graph.blocks[index];
            let &[next] = ir[block].succs.as_slice() else {
                continue;
            };
            if next == graph.last
                || next == graph.first
                || ends_with_switch(ir, block)
                || ir[next].preds.len() != 1
                || !ir[next].pred_exceptions.is_empty()
                || graph.exceptions.iter().any(|range| {
                    range.protected_range.contains(&block) != range.protected_range.contains(&next)
                })
            {
                continue;
            }

            let next_sequence = ir[next].seq.clone();
            let next_offsets = ir[next].instr_old_offsets.clone();
            ir[block].seq.add_sequence(&next_sequence);
            ir[block].instr_old_offsets.extend(next_offsets);
            ir[next].seq.clear();
            remove_empty_block(ir, graph, next, true, options);
            break;
        }

        if graph.blocks.len() == origin_block_count {
            break;
        }
    }
}

fn last_opcode(ir: &Ir, block: BlockId) -> Option<i32> {
    ir[block]
        .get_last_instruction()
        .map(|instruction| instruction.opcode)
}

fn ends_with_switch(ir: &Ir, block: BlockId) -> bool {
    ir[block]
        .get_last_instruction()
        .is_some_and(|instruction| instruction.group == GROUP_SWITCH)
}
