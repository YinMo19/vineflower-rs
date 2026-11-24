// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use std::{
    borrow::Cow,
    collections::{BTreeSet, HashSet},
};

use crate::{
    bytecode::{Instruction, Operand},
    cfg::ControlFlowGraph,
    lift::{BooleanCondition, BooleanFact, BooleanSelection, Machine},
    source_text::Document,
};

use super::{Arm, Emitter, Line, Region, StructureError, structure_regions, surrounded};

#[derive(Clone, Copy)]
struct ReturnTail {
    value: bool,
    transfer: u32,
    retested: bool,
}

impl ReturnTail {
    fn constant(value: bool, transfer: u32) -> Self {
        ReturnTail { value, transfer, retested: false }
    }
}

#[derive(Clone, Copy, Default)]
struct Suffix {
    empty: Option<ReturnTail>,
    operand: [Option<ReturnTail>; 2],
}

/// A stack boolean used only by forward jumps, zero tests and `ireturn`
/// can be returned at its producer instead. The new graph separates pure
/// return tails without copying any evaluation, and leaves real joins to
/// the ordinary structurer.
fn project(
    instructions: &[Instruction],
    graph: &ControlFlowGraph,
) -> Option<(Vec<Instruction>, ControlFlowGraph)> {
    if !graph.blocks.iter().any(|block| {
        block.predecessors.len() > 1 && block.instructions.len() == 1
            && matches!(instructions[block.instructions.start].opcode, 0x99 | 0x9a)
    }) {
        return None;
    }
    let mut suffix = vec![Suffix::default(); graph.blocks.len()];
    let mut producers = Vec::new();
    for (index, block) in graph.blocks.iter().enumerate().rev() {
        if block.successors.iter().any(|&next| next <= index) {
            continue;
        }
        let ops = &instructions[block.instructions.clone()];
        let jump = |op: &Instruction| matches!(op.opcode, 0xa7 | 0xc8);
        suffix[index] = match (ops, block.successors.as_slice()) {
            ([op], []) if op.opcode == 0xac => Suffix {
                empty: None,
                operand: [false, true].map(|value| Some(ReturnTail::constant(value, op.offset))),
            },
            ([op], &[next]) if jump(op) => suffix[next],
            ([op], &[taken, fallthrough]) if matches!(op.opcode, 0x99 | 0x9a) => {
                let (Some(taken), Some(fallthrough)) = (suffix[taken].empty, suffix[fallthrough].empty)
                else { continue };
                let shared = block.predecessors.len() > 1
                    && taken.transfer == fallthrough.transfer && taken.value != fallthrough.value;
                let operand = [false, true].map(|value| {
                    let mut tail = if value == (op.opcode == 0x9a) { taken } else { fallthrough };
                    tail.retested |= shared;
                    Some(tail)
                });
                Suffix { empty: None, operand }
            }
            ([push, rest @ ..], edges) if matches!(push.opcode, 0x03 | 0x04) => {
                let value = push.opcode == 0x04;
                let empty = match (rest, edges) {
                    ([ret], []) if ret.opcode == 0xac => Some(ReturnTail::constant(value, ret.offset)),
                    ([], &[next]) => suffix[next].operand[usize::from(value)],
                    ([op], &[next]) if jump(op) => suffix[next].operand[usize::from(value)],
                    _ => None,
                };
                if !edges.is_empty() && let Some(tail) = empty {
                    producers.push((index, tail));
                }
                Suffix { empty, ..Suffix::default() }
            }
            _ => continue,
        };
    }
    let transfers: BTreeSet<_> = producers.iter().filter(|(_, tail)| tail.retested)
        .map(|(_, tail)| tail.transfer).collect();
    if transfers.is_empty() {
        return None;
    }
    let mut cuts = vec![None; graph.blocks.len()];
    for (block, tail) in producers {
        if transfers.contains(&tail.transfer) {
            cuts[block] = Some(tail.value);
        }
    }
    let mut reachable = vec![false; graph.blocks.len()];
    let mut pending = vec![0];
    while let Some(block) = pending.pop() {
        if !std::mem::replace(&mut reachable[block], true) && cuts[block].is_none() {
            pending.extend(&graph.blocks[block].successors);
        }
    }
    let mut projected = Vec::with_capacity(instructions.len());
    for (index, block) in graph.blocks.iter().enumerate().filter(|(index, _)| reachable[*index]) {
        let ops = &instructions[block.instructions.clone()];
        let first = ops.first()?;
        if projected.last().is_some_and(|previous: &Instruction| previous.offset >= first.offset) {
            // The synthetic return would collide with a surviving entry.
            return None;
        }
        if let Some(value) = cuts[index] {
            projected.push(Instruction { opcode: if value { 0x04 } else { 0x03 }, ..first.clone() });
            projected.push(Instruction {
                offset: first.offset + first.len,
                opcode: 0xac,
                operand: Operand::None,
                len: 0,
            });
        } else {
            projected.extend_from_slice(ops);
        }
    }
    let graph = ControlFlowGraph::build(&projected, &[]).ok()?;
    Some((projected, graph))
}

pub(super) fn structure_with_boolean_tails(
    instructions: &[Instruction],
    graph: &ControlFlowGraph,
    machine: &mut Machine<'_, '_>,
) -> Option<Result<Vec<Line>, StructureError>> {
    if !machine.returns_boolean() || !machine.stack_is_empty() {
        return None;
    }
    let (projected, new_graph) = project(instructions, graph)?;
    let start = instructions.first()?.offset;
    let trial = machine.switch_arm_entry(&(start..=start)).ok()?;
    let names = machine.local_name_checkpoint();
    let sites = machine.switch_anonymous_checkpoint();
    Some(match structure_regions(instructions, graph, trial.clone(), &[], None, None) {
        Ok(lines) => {
            machine.commit_switch_dynamic_helpers(&trial);
            Ok(lines)
        }
        Err(error) => {
            machine.restore_local_names(names);
            machine.restore_switch_anonymous_sites(sites);
            if matches!(error, StructureError::Flow { .. }) {
                structure_regions(&projected, &new_graph, machine.clone(), &[], None, None)
            } else {
                Err(error)
            }
        }
    })
}

#[derive(Clone, Copy, Debug)]
pub(super) struct BooleanReturn {
    fact: BooleanFact,
    transfer: Option<u32>,
}

impl BooleanReturn {
    pub(super) fn direct(fact: BooleanFact, transfer: u32) -> Self {
        Self { fact, transfer: Some(transfer) }
    }

    fn take_value(line: &mut Line, used: bool) -> (BooleanFact, Cow<'static, Document>) {
        let returned = line.boolean_return.expect("a proven boolean return");
        if !used {
            return (returned.fact, Cow::Owned(Document::new()));
        }
        // Remove this emitter's own statement punctuation, not Java syntax
        // inferred from the value. Keep original layout events and tokens.
        let mut value = std::mem::take(&mut line.text);
        value.replace_literal_prefix("return ".len(), "");
        value.pop();
        (returned.fact, Cow::Owned(value))
    }
}

impl Emitter<'_> {
    /// Distinguish another terminal expression tree from the normal
    /// continuation of a guard clause. The lifted lines provide the final
    /// proof; this CFG check only controls whether we try both arms together.
    pub(super) fn pair_boolean_terminal_paths(&self, region: Region<'_, '_, '_>, entries: [usize; 2]) -> bool {
        let mut seen = HashSet::new();
        let mut pending = Vec::from(entries);
        while let Some(block) = pending.pop() {
            if !self.layout.inside(block, region)
                || self.emitted[block]
                || self.layout.loops[block].is_some()
                || self.exceptions.at_start(region.exception_arm, block).is_some()
                || !seen.insert(block)
            {
                return false;
            }
            let node = &self.graph.blocks[block];
            let instructions = &self.instructions[node.instructions.clone()];
            if instructions.iter().any(|op| matches!(op.opcode,
                0x36..=0x58 | 0x84 | 0xaa..=0xab | 0xb3 | 0xb5 | 0xc2..=0xc3))
            {
                return false;
            }
            if node.successors.is_empty() && instructions.last().is_none_or(|op| op.opcode != 0xac) {
                return false;
            }
            pending.extend(&node.successors);
        }
        true
    }

    pub(super) fn combine_boolean_returns(
        &mut self,
        arms: [&Arm<'_, '_>; 2],
        depth: usize,
        condition: (&Document, &Document, BooleanCondition),
    ) -> Option<Line> {
        let [yes, no] = arms;
        if yes.exit.is_some() || no.exit.is_some()
            || yes.end - yes.start != 1 || no.end - no.start != 1
        {
            return None;
        }
        let yes_fact = self.lines[yes.start].boolean_return?.fact;
        let no_fact = self.lines[no.start].boolean_return?.fact;
        let (condition, inverse, facts) = condition;
        let selection = BooleanSelection::of(facts, yes_fact, no_fact, true);
        let mut no = self.lines.pop().expect("last line of the false arm");
        let mut yes = self.lines.pop().expect("last line of the true arm");
        let (fact, value) = selection.render(
            (facts, [Cow::Borrowed(condition), Cow::Borrowed(inverse)]),
            BooleanReturn::take_value(&mut yes, selection.uses(true)),
            BooleanReturn::take_value(&mut no, selection.uses(false)),
        );
        let mut offsets = Vec::new();
        for (true_arm, line) in [(true, yes), (false, no)] {
            if selection.uses(true_arm) {
                let transfer = line.boolean_return.and_then(|value| value.transfer);
                offsets.extend(line.offsets.into_iter().filter(|offset| Some(*offset) != transfer));
            }
        }
        let mut line = Line::new(depth, surrounded(value, "return ", ";"), offsets);
        line.boolean_return = Some(BooleanReturn { fact, transfer: None });
        Some(line)
    }
}
