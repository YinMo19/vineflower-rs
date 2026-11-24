use std::collections::BTreeSet;

use crate::{bytecode::{Instruction, Operand}, cfg::{ControlFlowGraph, NaturalLoop}};

#[derive(Clone, Copy)]
pub(in crate::structure) struct LoopExitLabel {
    pub(in crate::structure) tail: usize,
    pub(in crate::structure) join: usize,
    pub(in crate::structure) break_count: usize,
}

impl LoopExitLabel {
    pub(in crate::structure) fn prove(
        graph: &ControlFlowGraph,
        instructions: &[Instruction],
        cycle: &NaturalLoop,
        normal: usize,
        exits: &BTreeSet<usize>,
    ) -> Option<Self> {
        let header = cycle.header;
        let inside = |block: usize| cycle.blocks.binary_search(&block).is_ok();
        if normal <= header || !exits.contains(&normal) {
            return None;
        }
        let mut join = None;
        let mut break_count = 0;
        for source in exits.iter().copied().filter(|&exit| exit != normal) {
            let node = &graph.blocks[source];
            let &[destination] = node.successors.as_slice() else { return None };
            let code = &instructions[node.instructions.clone()];
            let (jump, prefix) = code.split_last()?;
            if source <= header || source >= normal || !node.predecessors.iter().copied().all(inside)
                || !prefix.iter().all(|op| op.opcode == 0)
                || !matches!(jump.opcode, 0xa7 | 0xc8)
                || !matches!(jump.operand, Operand::Branch(_))
            {
                return None;
            }
            if destination != normal {
                if destination <= normal || join.is_some_and(|join| join != destination) {
                    return None;
                }
                join = Some(destination);
                break_count += 1;
            }
        }
        let join = join?;
        // The ordinary loop exit executes this private forward tail; the
        // alternate exits must skip all of it and agree on one continuation.
        for block in normal..join {
            let node = &graph.blocks[block];
            if node.successors != [block + 1]
                || node.predecessors.iter().any(|&pred| {
                    if block == normal { !inside(pred) && !exits.contains(&pred) }
                    else { pred + 1 != block }
                })
            {
                return None;
            }
        }
        if graph.blocks[join].predecessors.iter().any(|&pred| {
            let normal_edge = pred >= normal && pred + 1 == join;
            let abrupt_edge = pred > header && pred < normal && exits.contains(&pred);
            !normal_edge && !abrupt_edge
        }) {
            return None;
        }
        if (header..=join).any(|block| {
            let node = &graph.blocks[block];
            !node.exception_successors.is_empty() || !node.exception_predecessors.is_empty()
        }) {
            return None;
        }
        Some(Self { tail: normal, join, break_count })
    }
}
