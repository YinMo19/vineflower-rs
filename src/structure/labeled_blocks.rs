use std::{cell::RefCell, mem, ops::RangeInclusive};

use crate::{bytecode::Operand, lift::Machine};

use super::{Arm, Condition, Emitter, Line, Region, StructureError, instanceof_patterns};

pub(super) struct Scope<'a, 'c> {
    head: usize,
    tail: usize,
    join: usize,
    name: String,
    exits: RefCell<Vec<Exit<'a, 'c>>>,
}

struct Exit<'a, 'c> {
    block: usize,
    state: Machine<'a, 'c>,
}

#[derive(Debug, Clone, Copy)]
pub(super) enum EdgeLine {
    First(usize),
    Break(usize),
}

impl Scope<'_, '_> {
    pub(super) fn head_tail(&self, block: usize) -> Option<usize> {
        (self.head == block).then_some(self.tail)
    }
}

struct Plan {
    tail: usize,
    join: usize,
    break_count: usize,
}

impl Emitter<'_> {
    fn labeled_plan(
        &self,
        head: usize,
        region: Region<'_, '_, '_>,
        condition: &Condition,
        machine: &Machine<'_, '_>,
    ) -> Option<Plan> {
        // Bound the lexical scope to an ordinary forward region. A branch
        // into this interval from anywhere other than its head defeats
        // dominance; a transfer out of it before the join defeats ownership.
        if region.label_scope().is_some() || region.loop_header.is_some()
            || region.protected.is_some() || region.exception_arm.is_some()
        {
            return None;
        }
        let join = self.layout.normal_join(head, region)?;
        let tail = join.checked_sub(1)?;
        let inward = if condition.taken == tail { condition.fallthrough }
            else if condition.fallthrough == tail { condition.taken }
            else { return None; };
        if !(head < inward && inward < tail && tail < join)
            || !self.layout.inside(join, region) || !self.labeled_plain_block(join, region)
            || !self.labeled_plain_block(head, region)
        {
            return None;
        }
        let cfg = &self.graph.blocks;
        if cfg[tail].successors != [join] || self.explicit_jump(tail, join).is_some() {
            return None;
        }
        // A nested test must reach the same tail and have an independent
        // statement in its block. Without a statement, a boolean expression's
        // true/false materialization can have precisely the same CFG.
        if !cfg[tail].predecessors.iter().any(|&pred| {
            pred > head && pred < tail && cfg[pred].successors.len() == 2
                && branch(self.instructions[cfg[pred].instructions.end - 1].opcode)
                && self.instructions[cfg[pred].instructions.start..cfg[pred].instructions.end - 1]
                    .iter()
                    .any(|instruction| {
                        let index = match (instruction.opcode, &instruction.operand) {
                            (0xb6..=0xb8, Operand::Constant(index))
                            | (0xb9, Operand::InvokeInterface { index, .. }) => *index,
                            _ => return false,
                        };
                        machine.constant_pool().member_ref(index).is_ok_and(|(_, name, descriptor)| {
                            !name.starts_with('<') && descriptor.ends_with(")V")
                        })
                    })
        }) {
            return None;
        }
        let mut break_count = 0;
        for block in head..=tail {
            let node = &cfg[block];
            if block != head && (self.emitted[block] || !self.layout.inside(block, region)
                || !self.labeled_plain_block(block, region) || node.predecessors.is_empty()
                || node.predecessors.iter().any(|&pred| pred < head || pred >= block))
            {
                return None;
            }
            if node.successors.is_empty() || node.successors.iter().any(|&next| next <= block || next > join) {
                return None;
            }
            // This first proof handles conditions, not switch or handler
            // exits. Those need their own verified lexical edge projection.
            let last = &self.instructions[node.instructions.end - 1];
            if matches!(last.opcode, 0xaa | 0xab) { return None; }
            if block != tail && node.successors.contains(&join) {
                self.explicit_jump(block, join)?;
                break_count += 1;
            }
        }
        if break_count == 0 || cfg[join].predecessors.iter().any(|&pred| pred < head || pred > tail) {
            return None;
        }
        Some(Plan { tail, join, break_count })
    }

    fn labeled_plain_block(&self, block: usize, region: Region<'_, '_, '_>) -> bool {
        let node = &self.graph.blocks[block];
        self.exceptions.contains(region.exception_arm, block)
            && self.exceptions.at_start(region.exception_arm, block).is_none()
            && self.exceptions.bypass_cleanup(block) == block
            && !self.exception_redirects.contains_key(&block)
            && self.layout.loops[block].is_none()
            && node.exception_predecessors.is_empty() && node.exception_successors.is_empty()
            && node.instructions.clone().all(|index| {
                !self.exceptions.skips_instruction(index)
                    && !matches!(self.instructions[index].opcode, 0xc2 | 0xc3)
            })
    }

    fn explicit_jump(&self, block: usize, to: usize) -> Option<u32> {
        let jump = &self.instructions[self.graph.blocks[block].instructions.end - 1];
        match (jump.opcode, &jump.operand) {
            (0xa7 | 0xc8, Operand::Branch(target)) if self.graph.block_at(*target) == Some(to) => Some(jump.offset),
            _ => None,
        }
    }

    pub(super) fn emit_if_or_labeled<'a, 'c>(
        &mut self,
        head: usize,
        region: Region<'_, 'a, 'c>,
        machine: &mut Machine<'a, 'c>,
        depth: usize,
        condition: Condition,
        binding: Option<instanceof_patterns::Binding>,
        offsets: &mut Vec<u32>,
        control: RangeInclusive<u32>,
    ) -> Result<Option<usize>, StructureError> {
        let plan = if binding.is_none() && machine.this_is_initialized()
            && machine.stack_is_empty() && !self.assertion_starts(head)
        {
            self.labeled_plan(head, region, &condition, machine)
        } else { None };
        let Some(plan) = plan else {
            return self.emit_if(head, region, machine, depth, condition, binding, offsets, control);
        };
        let scope = Scope {
            head,
            tail: plan.tail,
            join: plan.join,
            name: format!("label{}", self.offset(plan.join)),
            exits: RefCell::new(Vec::with_capacity(plan.break_count)),
        };
        let label_region = region.label_body(&scope, Some(plan.join));
        let start = self.lines.len();
        let mut body = machine.clone();
        let next = self.emit_if(head, label_region, &mut body, depth + 1, condition, None, offsets, control)?;
        if next != Some(plan.tail) { return Err(self.unstructured(head)); }
        let boundary = self.lines.len();
        let normal = self.branch_arm(plan.tail, label_region, &body, depth + 1)?;
        if normal.exit.is_none() { return Err(self.unstructured(plan.tail)); }
        if boundary < self.lines.len() { self.lines[boundary].sequence_boundary = true; }
        let breaks = scope.exits.into_inner();
        if breaks.len() != plan.break_count { return Err(self.unstructured(head)); }
        let mut sites = vec![(None, None); breaks.len()];
        for (index, line) in self.lines.iter_mut().enumerate().skip(start).take(boundary - start) {
            match line.labeled_edge.take() {
                Some(EdgeLine::First(edge)) => sites[edge].0 = Some(index),
                Some(EdgeLine::Break(edge)) => sites[edge].1 = Some(index),
                None => {}
            }
        }
        let mut jumps = Vec::with_capacity(breaks.len());
        for (Exit { block, state }, (first, last)) in breaks.into_iter().zip(sites) {
            let end = last.ok_or_else(|| self.unstructured(block))?;
            jumps.push(Arm { exit: Some(state), offsets: Vec::new(), start: first.unwrap_or(end), end });
        }
        let arms: Vec<_> = jumps.iter().chain([&normal]).collect();
        let (declarations, assignments) = self.merge_arms(machine, plan.join, &arms)?;
        // Existing join code can hoist a fresh binding from the source origin
        // and retarget its sibling assignments. Any remaining typed copies
        // belong before the abrupt edge (or at the end of normal fallthrough).
        let mut edge_code: Vec<_> = arms.into_iter().zip(assignments).collect();
        edge_code.sort_unstable_by_key(|(arm, _)| arm.end);
        for (arm, statements) in edge_code.into_iter().rev() {
            let level = self.lines.get(arm.end).map_or(depth + 1, |line| line.depth);
            self.lines.splice(arm.end..arm.end, statements.into_iter().map(|text| Line::new(level, text, Vec::new())));
        }
        let label = Line::new(depth, format!("{}: {{", scope.name), Vec::new());
        self.lines.splice(start..start, declarations.into_iter().map(|text| Line::new(depth, text, Vec::new())).chain([label]));
        self.syntax(depth, "}");
        offsets.extend(normal.offsets);
        Ok(Some(plan.join))
    }

    pub(super) fn record_labeled_break<'a, 'c>(
        &mut self,
        block: usize,
        to: usize,
        region: Region<'_, 'a, 'c>,
        machine: &Machine<'a, 'c>,
        depth: usize,
        first_line: usize,
        offsets: &mut Vec<u32>,
    ) -> Result<bool, StructureError> {
        let Some(scope) = region.label_scope().filter(|scope| scope.join == to) else { return Ok(false); };
        if block <= scope.head || block >= scope.tail || !self.labeled_plain_block(block, region) {
            return Err(self.unstructured(block));
        }
        let jump = self.explicit_jump(block, to).ok_or_else(|| self.unstructured(block))?;
        let mut exits = scope.exits.borrow_mut();
        let edge = exits.len();
        exits.push(Exit { block, state: machine.clone() });
        if let Some(line) = self.lines.get_mut(first_line) {
            line.labeled_edge = Some(EdgeLine::First(edge));
        }
        offsets.push(jump);
        let mut line = Line::new(depth, format!("break {};", scope.name), mem::take(offsets));
        line.labeled_edge = Some(EdgeLine::Break(edge));
        self.lines.push(line);
        Ok(true)
    }
}

fn branch(opcode: u8) -> bool {
    matches!(opcode, 0x99..=0xa6 | 0xc6 | 0xc7)
}

#[cfg(test)]
mod tests;
