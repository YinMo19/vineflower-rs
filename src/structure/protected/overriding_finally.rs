// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use super::*;

/// A finally that saves a return value, then enters an enclosing resource's
/// normal close and a second finally that overrides the saved return. The
/// resource emitter still has to prove and own both close copies.
pub(in crate::structure) struct OverridingReturn {
    pub(in crate::structure) transfer: usize,
    pub(in crate::structure) normal_close: usize,
    pub(in crate::structure) exceptional_close: usize,
}

struct Path {
    value: Range<usize>,
    close: usize,
    terminal: usize,
}

impl Path {
    fn prove(
        instructions: &[Instruction],
        graph: &ControlFlowGraph,
        table: &Table,
        value_block: usize,
        skip_binding: usize,
    ) -> Option<Self> {
        let value = &graph.blocks[value_block];
        let value_code = value.instructions.start + skip_binding..value.instructions.end;
        let [load, store] = &instructions[value_code.clone()] else { return None };
        let resource = reference_load(load)?;
        let spill = reference_store(store)?;
        if resource == spill {
            return None;
        }
        let &[close] = value.successors.as_slice() else { return None };
        let close_block = &graph.blocks[close];
        let [receiver, invoke] = &instructions[close_block.instructions.clone()] else { return None };
        if reference_load(receiver) != Some(resource)
            || !matches!(invoke.opcode, 0xb6 | 0xb9)
            || close_block.predecessors != [value_block]
            || !close_block.exception_predecessors.is_empty()
        {
            return None;
        }
        let &[terminal] = close_block.successors.as_slice() else { return None };
        let [route] = table.by_block[close].as_slice() else { return None };
        if route.catch_type != 0
            || graph.blocks[terminal].predecessors != [close]
            || !table.by_block[terminal].is_empty()
            || !graph.blocks[terminal].successors.is_empty()
        {
            return None;
        }
        // The spill is overridden on both edges. Do not expose a different
        // local to either the outer normal return or its catch-all handler.
        let [.., returned] = &instructions[graph.blocks[terminal].instructions.clone()] else {
            return None;
        };
        if returned.opcode != 0xb0
            || instructions[graph.blocks[terminal].instructions.clone()].iter().any(|op| local_touches(op, spill))
        {
            return None;
        }
        let mut handler = route.handler;
        let binding = &graph.blocks[handler];
        let first = reference_store(&instructions[binding.instructions.start])?;
        if first == spill {
            return None;
        }
        let mut skip = 1;
        if binding.instructions.len() == 1 {
            let &[next] = binding.successors.as_slice() else { return None };
            handler = next;
            skip = 0;
        }
        let node = &graph.blocks[handler];
        if !node.successors.is_empty()
            || instructions[node.instructions.start + skip..node.instructions.end].iter().any(|op| local_touches(op, spill))
        {
            return None;
        }
        Some(Self { value: value_code, close, terminal })
    }
}

impl Exceptions {
    pub(super) fn prove_overriding_resource_finally(
        &mut self,
        instructions: &[Instruction],
        graph: &ControlFlowGraph,
        table: &Table,
        body: &BTreeSet<usize>,
        handler: usize,
    ) -> Option<Cleanup> {
        let entry = &graph.blocks[handler];
        if handler == 0 || body.contains(&handler) || !entry.predecessors.is_empty() {
            return None;
        }
        let saved = reference_store(&instructions[entry.instructions.start])?;
        let (block, skip_binding) = if entry.instructions.len() == 1 {
            let &[head] = entry.successors.as_slice() else { return None };
            if graph.blocks[head].predecessors != [handler]
                || !graph.blocks[head].exception_predecessors.is_empty()
            {
                return None;
            }
            (head, 0)
        } else {
            (handler, 1)
        };
        let exceptional = Path::prove(instructions, graph, table, block, skip_binding)?;
        let exits: BTreeSet<_> = normal_exits(graph, body).collect();
        let mut copies = exits.iter().copied();
        let copy = copies.next()?;
        if copies.next().is_some() {
            return None;
        }
        let normal = Path::prove(instructions, graph, table, copy, 0)?;
        if copy == block
            || body.contains(&block)
            || body.contains(&normal.close)
            || body.contains(&exceptional.close)
            || self.is_cleanup_copy(copy)
            || self.cleanup_prefixes.contains_key(&copy)
            || self.cleanup_landings.contains(&copy)
            || !self.terminal_cleanup_copies.contains(&normal.terminal)
            || !self.terminal_cleanup_copies.contains(&exceptional.terminal)
            || self.bypass_cleanup(normal.terminal) != self.bypass_cleanup(exceptional.terminal)
            || normal.close == exceptional.close
            || !graph.blocks[copy].exception_predecessors.is_empty()
            || graph.blocks[copy].predecessors.iter().any(|pred| !body.contains(pred))
            || table.by_block[copy] != table.by_block[block]
            || table.by_block[normal.close] != table.by_block[exceptional.close]
            || instructions[exceptional.value.clone()].iter().any(|op| local_touches(op, saved))
            || reference_load(&instructions[normal.value.start])
                != reference_load(&instructions[exceptional.value.start])
        {
            return None;
        }
        self.terminal_cleanup_copies.insert(copy);
        Some(Cleanup {
            start: handler,
            block,
            instructions: exceptional.value.start..exceptional.value.end - 1,
            branched: None,
            terminal_copies: Some(exits),
            overriding_return: Some(OverridingReturn {
                transfer: graph.blocks[exceptional.terminal].instructions.end - 1,
                normal_close: normal.close,
                exceptional_close: exceptional.close,
            }),
            spill_offsets: Vec::new(),
        })
    }
}
