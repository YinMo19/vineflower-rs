//! Control-flow changes made when recovering a finally handler.

use std::{io, sync::Arc};

use indexmap::IndexSet;
use rustc_hash::FxHashSet;

use super::{FinallyInfo, HandlerKind};
use crate::code::cfg::ControlFlowGraph;
use crate::code::code_constants::*;
use crate::code::{BytecodeVersion, Instruction};
use crate::decompiler::ir::{BlockId, Ir};

#[allow(clippy::too_many_arguments)]
pub(super) fn insert_semaphore(
    ir: &mut Ir,
    graph: &mut ControlFlowGraph,
    try_blocks: &IndexSet<BlockId>,
    head: BlockId,
    handler: BlockId,
    var: i32,
    info: &FinallyInfo,
    version: BytecodeVersion,
) -> io::Result<()> {
    let mut protected = try_blocks.clone();

    remove_exception_instructions(ir, handler, true, false, info.first_code)?;
    for (&last, &is_throw) in &info.last {
        if is_throw {
            remove_exception_instructions(ir, last, false, true, info.first_code)?;
            graph.finally_exits.insert(last);
        }
    }

    // Disable the semaphore at every exit from the try body. Replacement can
    // update more than one entry in a switch's successor list, so read each
    // entry from the live list rather than from a snapshot.
    for &block in try_blocks {
        for index in 0..ir[block].succs.len() {
            let destination = ir[block].succs[index];
            if destination == graph.last || protected.contains(&destination) {
                continue;
            }
            let clear = semaphore_block(ir, graph, var, false, version);
            block.replace_successor(ir, destination, clear);
            clear.add_successor(ir, destination);
            protected.insert(clear);
            copy_exception_edges(ir, graph, block, clear);
        }
    }

    let enable = semaphore_block(ir, graph, var, true, version);
    insert_block_before(ir, graph, head, enable);
    let initialize = semaphore_block(ir, graph, var, false, version);
    insert_block_before(ir, graph, enable, initialize);

    protected.insert(enable);
    protected.insert(initialize);
    for handler in ir[initialize].succ_exceptions.clone() {
        let range = graph
            .get_exception_range_mut(handler, initialize)
            .expect("missing protection for finally semaphore initialization");
        if range
            .protected_range
            .iter()
            .all(|block| protected.contains(block))
        {
            initialize.remove_successor_exception(ir, handler);
            if let Some(index) = range
                .protected_range
                .iter()
                .position(|&block| block == initialize)
            {
                range.protected_range.remove(index);
            }
        }
    }
    Ok(())
}

fn semaphore_block(
    ir: &mut Ir,
    graph: &mut ControlFlowGraph,
    var: i32,
    enabled: bool,
    version: BytecodeVersion,
) -> BlockId {
    let block = graph.new_block(ir);
    let store_length = if var <= 3 {
        1
    } else if var <= 128 {
        2
    } else {
        4
    };
    for (opcode, operand, length) in [
        (OPC_BIPUSH, i32::from(enabled), 1),
        (OPC_ISTORE, var, store_length),
    ] {
        let instruction = Instruction::create(
            opcode,
            false,
            GROUP_GENERAL,
            version,
            vec![operand],
            -1,
            length,
        );
        ir[block].seq.add_instruction(Arc::new(instruction));
    }
    block
}

fn copy_exception_edges(ir: &mut Ir, graph: &mut ControlFlowGraph, source: BlockId, copy: BlockId) {
    for handler in ir[source].succ_exceptions.clone() {
        copy.add_successor_exception(ir, handler);
        graph
            .get_exception_range_mut(handler, source)
            .expect("missing range for finally semaphore")
            .protected_range
            .push(copy);
    }
}

fn insert_block_before(ir: &mut Ir, graph: &mut ControlFlowGraph, old: BlockId, new: BlockId) {
    for predecessor in old.get_predecessors(ir) {
        predecessor.replace_successor(ir, old, new);
    }
    copy_exception_edges(ir, graph, old, new);
    for range in &mut graph.exceptions {
        if range.handler == old {
            range.handler = new;
        }
    }
    new.add_successor(ir, old);
    if graph.first == old {
        graph.first = new;
    }
}

pub(super) fn delete_area(
    ir: &mut Ir,
    graph: &mut ControlFlowGraph,
    start: BlockId,
    sample: &IndexSet<BlockId>,
    next: Option<BlockId>,
) {
    if Some(start) == next {
        return;
    }
    let next = next.unwrap_or(graph.last);

    let mut common_handlers: FxHashSet<_> = ir[next].succ_exceptions.iter().copied().collect();
    for &predecessor in &ir[start].preds {
        common_handlers.retain(|handler| ir[predecessor].succ_exceptions.contains(handler));
    }

    let predecessors: IndexSet<_> = ir[start].preds.iter().copied().collect();
    for &predecessor in &predecessors {
        predecessor.replace_successor(ir, start, next);
    }

    // Exception ranges are Java objects, including when they are removed from
    // the graph. Give them stable local names so a later entry at the same
    // vector index, or an identical range, cannot stand in for a removed one.
    let handlers: Vec<_> = graph.exceptions.iter().map(|range| range.handler).collect();
    let mut range_ids: Vec<_> = (0..handlers.len()).collect();
    let mut removed = Vec::new();
    let mut common_ranges: Option<IndexSet<usize>> = None;
    let mut outside = false;

    for &block in sample {
        // A split block can appear in more than one area.
        if !graph.blocks.contains_key(&ir[block].id) {
            continue;
        }

        outside |= common_handlers
            .iter()
            .any(|handler| !ir[block].succ_exceptions.contains(handler));
        let ranges: IndexSet<_> = ir[block]
            .succ_exceptions
            .iter()
            .map(|&handler| {
                let index = graph
                    .get_exception_range_index(handler, block)
                    .expect("missing exception range for finally area");
                range_ids[index]
            })
            .collect();
        if let Some(common) = &mut common_ranges {
            common.retain(|range| ranges.contains(range));
        } else {
            common_ranges = Some(ranges);
        }

        if ir[block].seq.is_empty() && ir[block].succs.len() == 1 {
            let successor = ir[block].succs[0];
            for predecessor in ir[block].preds.clone() {
                if !sample.contains(&predecessor) {
                    predecessor.replace_successor(ir, block, successor);
                }
            }
            if graph.first == block {
                graph.first = successor;
            }
        }
        graph.remove_block_tracking_ranges(ir, block, |index| removed.push(index));
        for index in removed.drain(..).rev() {
            range_ids.remove(index);
        }
    }

    if outside {
        let bridge = graph.new_block(ir);
        for range in common_ranges.unwrap() {
            bridge.add_successor_exception(ir, handlers[range]);
            if let Ok(index) = range_ids.binary_search(&range) {
                graph.exceptions[index].protected_range.push(bridge);
            }
        }
        bridge.add_successor(ir, next);
        for predecessor in predecessors {
            predecessor.replace_successor(ir, next, bridge);
        }
    }
}

pub(super) fn remove_exception_instructions(
    ir: &mut Ir,
    block: BlockId,
    first: bool,
    last: bool,
    kind: HandlerKind,
) -> io::Result<()> {
    let block = &mut ir[block];
    if kind == HandlerKind::Empty {
        for index in (0..block.seq.length()).rev() {
            block.seq.remove_instruction(index);
            remove_old_offset(&mut block.instr_old_offsets, index)?;
        }
        return Ok(());
    }
    if first && matches!(kind, HandlerKind::Pop | HandlerKind::Store) {
        if block.seq.is_empty() {
            return Err(invalid_removal_index("finally instruction removal", 0, 0));
        }
        block.seq.remove_instruction(0);
        remove_old_offset(&mut block.instr_old_offsets, 0)?;
    }
    if last && matches!(kind, HandlerKind::Stack | HandlerKind::Store) {
        let count = if kind == HandlerKind::Store { 2 } else { 1 };
        for _ in 0..count {
            block.seq.remove_last();
            let index = block.instr_old_offsets.len() as i32 - 1;
            remove_old_offset(&mut block.instr_old_offsets, index)?;
        }
    }
    Ok(())
}

fn remove_old_offset(offsets: &mut Vec<i32>, index: i32) -> io::Result<()> {
    if index as usize >= offsets.len() {
        return Err(invalid_removal_index(
            "finally instruction offset removal",
            index,
            offsets.len(),
        ));
    }
    offsets.remove(index as usize);
    Ok(())
}

fn invalid_removal_index(operation: &str, index: i32, length: usize) -> io::Error {
    io::Error::new(
        io::ErrorKind::InvalidData,
        format!("{operation}: Index {index} out of bounds for length {length}"),
    )
}

pub(super) fn inline_return_var(
    ir: &mut Ir,
    graph: &mut ControlFlowGraph,
    handler: BlockId,
    info: &FinallyInfo,
) {
    let mut exits = IndexSet::new();
    for range in graph
        .exceptions
        .iter()
        .filter(|range| range.handler == handler)
    {
        for &block in &range.protected_range {
            if ir[block]
                .succs
                .iter()
                .any(|&successor| ir[successor].succ_exceptions != ir[block].succ_exceptions)
            {
                exits.insert(block);
            }
        }
    }

    for exit in exits {
        let [successor] = ir[exit].succs.as_slice() else {
            continue;
        };
        let successor = *successor;
        let Some(store) = ir[exit].get_last_instruction() else {
            continue;
        };
        if !(OPC_ISTORE..=OPC_ASTORE).contains(&store.opcode)
            || ir[successor].preds.len() != 1
            || !ir[successor].pred_exceptions.is_empty()
            || ir[successor].seq.length() != 2
        {
            continue;
        }
        let load = ir[successor].get_instruction(0);
        let ret = ir[successor].get_instruction(1);
        let offset = store.opcode - OPC_ISTORE;
        if load.start_offset < info.exception_offset
            && load.opcode == OPC_ILOAD + offset
            && ret.opcode == OPC_IRETURN + offset
            && load.operand(0) == store.operand(0)
        {
            let ret = Arc::clone(ret);
            ir[exit].seq.remove_last();
            ir[exit].seq.add_instruction(ret);
            // As in upstream, offset lists remain with their original blocks
            // until the subsequent empty-block and block-merge passes.
            ir[successor].seq.clear();
        }
    }
}
