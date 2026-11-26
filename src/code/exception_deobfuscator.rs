// Copyright 2000-2020 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! `modules.code.ExceptionDeobfuscator`: repairs and normalizes CFG exception ranges.

use std::collections::VecDeque;
use std::sync::Arc;

use indexmap::{IndexMap, IndexSet};
use rustc_hash::{FxHashMap, FxHashSet};

use super::cfg::{ControlFlowGraph, ExceptionRangeCFG};
use super::code_constants::{GROUP_GENERAL, OPC_ASTORE, OPC_BIPUSH, OPC_NEW, OPC_POP};
use super::{Instruction, InstructionSequence};
use crate::decompiler::decompose::generic_dominator_engine::GenericDominatorEngine;
use crate::decompiler::ir::{BlockId, Ir};
use crate::engine::method_timeout::checkpoint;
use crate::engine::Options;
use crate::structs::StructClass;

struct AggregatedRange {
    representative: usize,
    protected: FxHashSet<BlockId>,
}

pub fn restore_pop_ranges(ir: &mut Ir, graph: &mut ControlFlowGraph) {
    let mut ranges = IndexMap::new();
    for (index, range) in graph.exceptions.iter().enumerate() {
        ranges
            .entry((range.handler, range.get_unique_exceptions_string()))
            .or_insert_with(|| AggregatedRange {
                representative: index,
                protected: FxHashSet::default(),
            })
            .protected
            .extend(range.protected_range.iter().copied());
    }

    for ((original_handler, exception_types), range) in &ranges {
        checkpoint();
        if exception_types.is_none() {
            continue;
        }
        let mut handler = *original_handler;
        let Some(first_instruction) = ir[handler]
            .seq
            .iter()
            .next()
            .filter(|instr| matches!(instr.opcode, OPC_POP | OPC_ASTORE))
            .cloned()
        else {
            continue;
        };

        for ((outer_handler, outer_types), outer) in &ranges {
            if outer.representative == range.representative
                || range.protected.contains(outer_handler)
                || outer.protected.contains(&handler)
            {
                continue;
            }
            let inherits_protection = if outer_types.is_none() {
                !outer.protected.is_disjoint(&range.protected)
            } else {
                outer.protected.len() > range.protected.len()
                    && outer.protected.is_superset(&range.protected)
            };
            if !inherits_protection {
                continue;
            }

            let mut new_handler = handler;
            if ir[handler].seq.length() > 1 {
                new_handler = graph.new_block(ir);
                let instruction = Arc::new(first_instruction.as_ref().clone());
                ir[new_handler].seq.add_instruction(instruction);

                let predecessors = handler.get_predecessors(ir);
                insert_handler_before(ir, graph, handler, new_handler, predecessors);
                ir[handler].seq.remove_instruction(0);
            }

            new_handler.add_successor_exception(ir, *outer_handler);
            graph.exceptions[outer.representative]
                .protected_range
                .push(new_handler);

            // The aggregate keeps the original handler, while its range can be updated above.
            handler = graph.exceptions[range.representative].handler;
        }
    }
}

pub fn insert_empty_exception_handler_blocks(ir: &mut Ir, graph: &mut ControlFlowGraph) {
    let mut visited = FxHashSet::default();
    for index in 0..graph.exceptions.len() {
        let handler = graph.exceptions[index].handler;
        if visited.insert(handler) {
            let empty = graph.new_block(ir);
            let predecessors = ir[handler].pred_exceptions.clone();
            insert_handler_before(ir, graph, handler, empty, predecessors);
        }
    }
}

fn insert_handler_before(
    ir: &mut Ir,
    graph: &mut ControlFlowGraph,
    handler: BlockId,
    replacement: BlockId,
    predecessors: Vec<BlockId>,
) {
    for predecessor in predecessors {
        predecessor.replace_successor(ir, handler, replacement);
    }

    for range in &mut graph.exceptions {
        if range.handler == handler {
            range.handler = replacement;
        } else if range.protected_range.contains(&handler) {
            replacement.add_successor_exception(ir, range.handler);
            range.protected_range.push(replacement);
        }
    }

    replacement.add_successor(ir, handler);
    if graph.first == handler {
        graph.first = replacement;
    }
}

pub fn remove_empty_ranges(ir: &mut Ir, graph: &mut ControlFlowGraph) {
    for index in (0..graph.exceptions.len()).rev() {
        let range = &graph.exceptions[index];
        if range
            .protected_range
            .iter()
            .all(|&block| ir[block].seq.is_empty())
        {
            for &block in &range.protected_range {
                block.remove_successor_exception(ir, range.handler);
            }

            graph.exceptions.remove(index);
            graph.add_comment("$VF: Removed empty exception range");
        }
    }
}

pub fn remove_circular_ranges(ir: &mut Ir, graph: &mut ControlFlowGraph) {
    let mut dominators = None;
    for index in (0..graph.exceptions.len()).rev() {
        if !graph.exceptions[index].is_circular() {
            continue;
        }

        // Use one snapshot taken before any exception edges are removed.
        let engine = dominators.get_or_insert_with(|| GenericDominatorEngine::for_cfg(ir, graph));
        let range = &mut graph.exceptions[index];
        let reachable = get_reachable_blocks_restricted(ir, range.handler, range, engine);
        if reachable.len() < range.protected_range.len() || range.protected_range.len() == 1 {
            for block in reachable {
                block.remove_successor_exception(ir, range.handler);
                if let Some(index) = range.protected_range.iter().position(|&item| item == block) {
                    range.protected_range.remove(index);
                }
            }
        }
        if range.protected_range.is_empty() {
            graph.exceptions.remove(index);
        }
    }
}

fn get_reachable_blocks_restricted(
    ir: &Ir,
    start: BlockId,
    range: &ExceptionRangeCFG,
    dominators: &GenericDominatorEngine<BlockId>,
) -> Vec<BlockId> {
    let protected: FxHashSet<_> = range.protected_range.iter().copied().collect();
    let mut reachable = Vec::new();
    let mut pending = VecDeque::from([start]);
    let mut visited = FxHashSet::default();

    while let Some(block) = pending.pop_front() {
        checkpoint();
        visited.insert(block);
        if protected.contains(&block) && dominators.is_dominator(block, start) {
            reachable.push(block);
            pending.extend(
                ir[block]
                    .succs
                    .iter()
                    .chain(&ir[block].succ_exceptions)
                    .filter(|successor| !visited.contains(*successor))
                    .copied(),
            );
        }
    }

    reachable
}

pub fn has_obfuscated_exceptions(ir: &Ir, graph: &ControlFlowGraph) -> bool {
    let mut protected_by_handler: FxHashMap<_, FxHashSet<_>> = FxHashMap::default();
    for range in &graph.exceptions {
        protected_by_handler
            .entry(range.handler)
            .or_default()
            .extend(range.protected_range.iter().copied());
    }

    protected_by_handler.values().any(|protected| {
        protected
            .iter()
            .copied()
            .filter(|&block| block == graph.first || has_external_predecessor(ir, block, protected))
            .nth(1)
            .is_some()
    })
}

pub fn handle_multiple_entry_exception_ranges(ir: &mut Ir, graph: &mut ControlFlowGraph) -> bool {
    handle_multiple_entry_exception_ranges_with(ir, graph, warn_inconsistent_split)
}

pub(crate) fn warn_inconsistent_split() {
    log::warn!("Inconsistency found while splitting protected range");
}

pub(crate) fn handle_multiple_entry_exception_ranges_with(
    ir: &mut Ir,
    graph: &mut ControlFlowGraph,
    mut on_inconsistent_split: impl FnMut(),
) -> bool {
    let dominators = GenericDominatorEngine::for_cfg(ir, graph);
    loop {
        let mut found_multiple = false;
        let mut split = false;
        for index in 0..graph.exceptions.len() {
            checkpoint();
            let entries = get_range_entries(ir, &graph.exceptions[index]);
            if entries.len() <= 1 {
                continue;
            }

            found_multiple = true;
            if split_exception_range(
                ir,
                graph,
                index,
                &entries,
                &dominators,
                &mut on_inconsistent_split,
            ) {
                split = true;
                graph.add_comment(
                    "$VF: Handled exception range with multiple entry points by splitting it",
                );
                break;
            }
        }
        if !split {
            return !found_multiple;
        }
    }
}

fn get_range_entries(ir: &Ir, range: &ExceptionRangeCFG) -> IndexSet<BlockId> {
    let protected: FxHashSet<_> = range.protected_range.iter().copied().collect();
    range
        .protected_range
        .iter()
        .copied()
        .filter(|&block| has_external_predecessor(ir, block, &protected))
        .collect()
}

fn has_external_predecessor(ir: &Ir, block: BlockId, protected: &FxHashSet<BlockId>) -> bool {
    ir[block].preds.iter().any(|pred| !protected.contains(pred))
}

fn split_exception_range(
    ir: &Ir,
    graph: &mut ControlFlowGraph,
    index: usize,
    entries: &IndexSet<BlockId>,
    dominators: &GenericDominatorEngine<BlockId>,
    on_inconsistent_split: &mut impl FnMut(),
) -> bool {
    for &entry in entries {
        let range = &graph.exceptions[index];
        let reachable = get_reachable_blocks_restricted(ir, entry, range, dominators);
        if !reachable.is_empty() && reachable.len() < range.protected_range.len() {
            let moved: FxHashSet<_> = reachable.iter().copied().collect();
            graph.exceptions.push(ExceptionRangeCFG::new(
                reachable,
                range.handler,
                range.exception_types.clone(),
            ));
            graph.exceptions[index]
                .protected_range
                .retain(|block| !moved.contains(block));
            return true;
        }

        on_inconsistent_split();
    }
    false
}

pub fn insert_dummy_exception_handler_blocks(
    ir: &mut Ir,
    graph: &mut ControlFlowGraph,
    class: &StructClass,
    options: &Options,
) {
    let mut ranges_by_handler = IndexMap::<_, Vec<_>>::new();
    for (index, range) in graph.exceptions.iter().enumerate() {
        ranges_by_handler
            .entry(range.handler)
            .or_default()
            .push(index);
    }

    for (handler, ranges) in ranges_by_handler {
        if ranges.len() == 1 {
            continue;
        }

        if options.old_try_dedup {
            for index in ranges {
                insert_dummy_handler(ir, graph, class, handler, index);
            }
        } else {
            for &index in ranges.iter().skip(1) {
                duplicate_handler(ir, graph, handler, index);
            }

            if !is_match_exception(ir, class, handler) {
                graph.add_comment(
                    "$VF: Duplicated exception handlers to handle obfuscated exceptions",
                );
            }
        }
    }
}

fn duplicate_handler(ir: &mut Ir, graph: &mut ControlFlowGraph, handler: BlockId, index: usize) {
    let new_block = graph.new_block(ir);
    ir[new_block].seq = ir[handler].seq.clone();
    replace_range_handler(ir, &mut graph.exceptions[index], handler, new_block);

    for successor in ir[handler].succs.clone() {
        new_block.add_successor(ir, successor);
    }
    for successor in ir[handler].succ_exceptions.clone() {
        new_block.add_successor_exception(ir, successor);
        graph
            .get_exception_range_mut(successor, handler)
            .expect("Missing exception range for handler successor")
            .protected_range
            .push(new_block);
    }
}

fn insert_dummy_handler(
    ir: &mut Ir,
    graph: &mut ControlFlowGraph,
    class: &StructClass,
    handler: BlockId,
    index: usize,
) {
    // Keep the dummy block non-empty so later passes retain it.
    let sequence = InstructionSequence::from_collection(
        [(OPC_BIPUSH, vec![0]), (OPC_POP, Vec::new())]
            .into_iter()
            .map(|(opcode, operands)| {
                Arc::new(Instruction::create(
                    opcode,
                    false,
                    GROUP_GENERAL,
                    class.version,
                    operands,
                    -1,
                    1,
                ))
            }),
    );
    let dummy = graph.new_block(ir);
    ir[dummy].seq = sequence;
    let predecessors = replace_range_handler(ir, &mut graph.exceptions[index], handler, dummy);

    let mut common_handlers: IndexSet<_> = ir[handler].succ_exceptions.iter().copied().collect();
    for predecessor in predecessors {
        common_handlers.retain(|target| ir[predecessor].succ_exceptions.contains(target));
    }
    for common_handler in common_handlers {
        let range = graph
            .get_exception_range_mut(common_handler, handler)
            .expect("Missing exception range for common handler");
        dummy.add_successor_exception(ir, common_handler);
        range.protected_range.push(dummy);
    }

    dummy.add_successor(ir, handler);
    graph.add_comment("$VF: Inserted dummy exception handlers to handle obfuscated exceptions");
}

fn replace_range_handler(
    ir: &mut Ir,
    range: &mut ExceptionRangeCFG,
    handler: BlockId,
    replacement: BlockId,
) -> Vec<BlockId> {
    let protected: FxHashSet<_> = range.protected_range.iter().copied().collect();
    let predecessors: Vec<_> = ir[handler]
        .pred_exceptions
        .iter()
        .filter(|pred| protected.contains(*pred))
        .copied()
        .collect();
    for &predecessor in &predecessors {
        predecessor.replace_successor(ir, handler, replacement);
    }
    range.handler = replacement;
    predecessors
}

fn is_match_exception(ir: &Ir, class: &StructClass, handler: BlockId) -> bool {
    ir[handler].seq.iter().any(|instruction| {
        instruction.opcode == OPC_NEW
            && class
                .pool
                .get_primitive_constant(instruction.operand(0))
                .unwrap()
                .get_string()
                .as_str()
                == "java/lang/MatchException"
    })
}
