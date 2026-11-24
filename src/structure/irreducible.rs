// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use std::mem;

use crate::bytecode::Instruction;
use crate::cfg::ControlFlowGraph;
use crate::lift::{Effect, Machine};

use super::do_while::is_conditional;
use super::flow::Layout;
use super::{Emitter, Region, StructureError};

pub(super) struct Cycle {
    header: usize,
    members: Vec<bool>,
    remaining_instructions: usize,
}

impl Cycle {
    /// Only cut a closed, straight-line cycle with an acyclic inlet. It is
    /// safe to roll each entry forward to the chosen header: none of these
    /// copies can branch away from that header or repeat an entire cycle.
    pub(super) fn prove(
        instructions: &[Instruction],
        graph: &ControlFlowGraph,
        layout: &Layout,
    ) -> Option<Self> {
        if layout.loops.iter().any(Option::is_some)
            || !graph.blocks.iter().enumerate().any(|(block, node)| {
                node.successors.iter().any(|&next| next < block)
            })
        {
            return None;
        }
        let mut reachable = graph.reachable();
        let members = {
            let mut cycles = graph.strongly_connected_components().into_iter().filter(|component| {
                let block = component[0];
                reachable[block]
                    && (component.len() > 1 || graph.blocks[block].successors.contains(&block))
            });
            let members = cycles.next()?;
            if cycles.next().is_some() {
                return None;
            }
            members
        };
        if members.len() < 2 || members.iter().any(|&block| {
            let node = &graph.blocks[block];
            let tail = instructions[node.instructions.end - 1].opcode;
            node.successors.len() != 1 || is_conditional(tail) || matches!(tail, 0xaa | 0xab)
        }) {
            return None;
        }

        let header = {
            // In a strongly connected component with one successor per
            // member, each member has exactly one predecessor in the cycle.
            let mut entries = members.iter().copied().filter(|&block| {
                block == 0 || graph.blocks[block].predecessors.iter()
                    .filter(|&&pred| reachable[pred]).nth(1).is_some()
            });
            let first = entries.next()?;
            entries.max()?.max(first)
        };
        if members.iter().copied().filter(|&block| block != header).any(|block| {
            // Don't duplicate dynamic call sites or allocations that might
            // introduce a distinct source-local or anonymous class.
            instructions[graph.blocks[block].instructions.clone()].iter()
                .any(|op| matches!(op.opcode, 0xba | 0xbb))
        }) {
            return None;
        }
        reachable.fill(false);
        for block in members {
            reachable[block] = true;
        }
        Some(Self { header, members: reachable, remaining_instructions: instructions.len() })
    }
}

impl Emitter<'_> {
    pub(super) fn emit_irreducible_cycle(
        &mut self,
        cycle: Cycle,
        machine: &mut Machine<'_, '_>,
    ) -> Result<(), StructureError> {
        let header = cycle.header;
        // Postdominance sees a terminal at the header, but lifting and local
        // liveness still see the original instructions, offsets and edges.
        self.layout.cut_at_cycle_entry(self.graph, header);
        self.cycle_rollout = Some(cycle);
        if !self.region(0, Region::METHOD.branch(Some(header)), machine, 0)? {
            return Err(self.unstructured(header));
        }
        let cycle = self.cycle_rollout.take().expect("rollout is active");
        self.layout.install_closed_cycle(header, &cycle.members);
        for (block, member) in cycle.members.into_iter().enumerate() {
            if member {
                self.emitted[block] = false;
            }
        }
        if self.region(header, Region::METHOD, machine, 0)? {
            return Err(self.unstructured(header));
        }
        Ok(())
    }

    pub(super) fn try_cycle_rollout<'a, 'c>(
        &mut self,
        block: usize,
        region: Region<'_, 'a, 'c>,
        machine: &mut Machine<'a, 'c>,
        depth: usize,
        pending: &mut Vec<u32>,
        first_instruction: Option<usize>,
    ) -> Result<Option<usize>, StructureError> {
        let Some(cycle) = self.cycle_rollout.as_mut() else { return Ok(None) };
        if block == cycle.header || !cycle.members[block] {
            return Ok(None);
        }
        if first_instruction.is_some() || !self.layout.inside(block, region) {
            return Err(self.unstructured(block));
        }
        // Stop pathological inlet fan-in from generating quadratic output.
        let Some(remaining) = cycle.remaining_instructions
            .checked_sub(self.graph.blocks[block].instructions.len())
        else {
            return Err(self.unstructured(block));
        };
        cycle.remaining_instructions = remaining;
        let tail = self.lift_block(block, machine, region, depth, mem::take(pending))?;
        let next = self.single_successor(block)?;
        match tail.effect {
            Effect::None => {}
            Effect::Jump(target) if self.graph.block_at(target) == Some(next) => {}
            _ => return Err(self.unstructured(block)),
        }
        *pending = tail.offsets;
        // Leave the original block available to other entries and the loop.
        Ok(Some(next))
    }
}
