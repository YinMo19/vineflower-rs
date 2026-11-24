// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use crate::bytecode::Instruction;
use crate::cfg::ControlFlowGraph;
use crate::classfile::ExceptionHandler;

use super::StructureError;

#[derive(Clone, Copy)]
pub(super) struct Try {
    pub(super) start: usize,
    pub(super) end: usize,
    pub(super) handler: usize,
    pub(super) catch_type: u16,
    pub(super) join: Option<usize>,
    pub(super) return_split: Option<usize>,
    trampoline: Option<usize>,
}

impl Try {
    pub(super) fn new(
        instructions: &[Instruction],
        graph: &ControlFlowGraph,
        handlers: &[ExceptionHandler],
    ) -> Result<Self, StructureError> {
        let unsupported = || StructureError::ExceptionHandlers;
        let [entry] = handlers else {
            return Err(unsupported());
        };
        // Do not infer catch ordering, overlap, or finally semantics from a
        // graph which has more than one protected table entry.
        if entry.catch_type == 0 {
            return Err(unsupported());
        }
        let start = graph
            .block_at(entry.start_pc.into())
            .ok_or_else(unsupported)?;
        let handler = graph
            .block_at(entry.handler_pc.into())
            .ok_or_else(unsupported)?;
        let end = if let Some(end) = graph.block_at(entry.end_pc.into()) {
            end
        } else if instructions
            .last()
            .is_some_and(|last| last.offset + last.len == u32::from(entry.end_pc))
        {
            graph.blocks.len()
        } else {
            return Err(unsupported());
        };
        let protected = start..end;
        if start >= end
            || handler == 0
            || protected.contains(&handler)
            || !graph.blocks[handler].predecessors.is_empty()
        {
            return Err(unsupported());
        }
        let mut join = None;
        for (block, node) in graph.blocks.iter().enumerate() {
            if protected.contains(&block) {
                if node.exception_successors != [handler]
                    || (block != start
                        && node
                            .predecessors
                            .iter()
                            .any(|pred| !protected.contains(pred)))
                {
                    return Err(unsupported());
                }
                for &next in &node.successors {
                    if !protected.contains(&next) {
                        if next != end {
                            return Err(unsupported());
                        }
                        join = Some(end);
                    }
                }
            } else if !node.exception_successors.is_empty() {
                return Err(unsupported());
            }
        }

        let mut return_split = None;
        let mut trampoline = None;
        if let Some(exit) = join {
            let node = &graph.blocks[exit];
            if node.instructions.len() == 1
                && node
                    .predecessors
                    .iter()
                    .all(|pred| protected.contains(pred))
            {
                let exit_opcode = instructions[node.instructions.start].opcode;
                match exit_opcode {
                    0xa7 | 0xc8 => {
                        let [destination] = node.successors.as_slice() else {
                            return Err(unsupported());
                        };
                        if protected.contains(destination)
                            || *destination == handler
                            || *destination == exit
                        {
                            return Err(unsupported());
                        }
                        join = Some(*destination);
                        trampoline = Some(exit);
                    }
                    0xac..=0xb1 => {
                        // javac commonly excludes the non-throwing return
                        // opcode from the protected interval. Keep its
                        // potentially throwing value computation in the try
                        // by fusing this exclusive fallthrough split.
                        if let [pred] = node.predecessors.as_slice() {
                            let predecessor = &graph.blocks[*pred];
                            if predecessor.instructions.end == node.instructions.start
                                && predecessor.successors == [exit]
                                && !matches!(instructions[predecessor.instructions.end - 1].opcode, 0x99..=0xab | 0xc6..=0xc9)
                            {
                                join = None;
                                return_split = Some(exit);
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
        Ok(Self {
            start,
            end,
            handler,
            catch_type: entry.catch_type,
            join,
            return_split,
            trampoline,
        })
    }

    pub(super) fn contains(&self, block: usize) -> bool {
        (self.start..self.end).contains(&block) || self.trampoline == Some(block)
    }
}
