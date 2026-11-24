use std::{cell::RefCell, collections::BTreeSet, mem, ops::RangeInclusive};

use crate::{bytecode::Operand, lift::Machine, source_text::Document};

use super::{
    Arm, Condition, Emitter, Line, Region, StructureError, instanceof_patterns,
    protected::{ArmId, MonitorDeparture, ProtectedRegion},
    flow::Loop,
};

mod resource_switch;

pub(super) struct Scope<'a, 'c> {
    head: usize,
    tail: usize,
    join: usize,
    name: String,
    edges: Edges,
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
        (self.head == block
            && !matches!(&self.edges, Edges::Monitor { branch_tail: false, .. } | Edges::Finally { .. }))
        .then_some(self.tail)
    }

    pub(super) fn owns_monitor_departure(&self, arm: ArmId, departure: MonitorDeparture) -> bool {
        matches!(
            &self.edges,
            Edges::Monitor { arm: owner, edge, .. }
                if *owner == arm && edge.source == departure.source && edge.target == departure.target
        )
    }
}

struct Plan {
    tail: usize,
    join: usize,
    break_count: usize,
    edges: Edges,
}

enum Edges {
    Explicit,
    Resource { arm: ArmId, abrupt_entries: BTreeSet<usize> },
    Monitor { arm: ArmId, edge: MonitorDeparture, branch_tail: bool },
    Finally { body: ArmId, entry: usize, jump: usize },
}

enum Head {
    If(Condition),
    Switch(Document),
}

impl Emitter<'_> {
    pub(super) fn emit_loop_with_finally_label<'a, 'c>(
        &mut self,
        header: usize,
        loop_shape: Loop,
        region: Region<'_, 'a, 'c>,
        machine: &mut Machine<'a, 'c>,
        depth: usize,
    ) -> Result<Option<usize>, StructureError> {
        let exceptions = self.exceptions;
        let Some(shape) = exceptions.at_start(region.exception_arm, header)
            .map(|id| exceptions.region(id))
        else { return Ok(None); };
        let Some(finally) = &shape.finally else { return Ok(None); };
        let Some(plan) = finally.branched().and_then(|branch| branch.label.as_ref())
        else { return Ok(None); };
        let Some(test) = loop_shape.post_test else { return Err(self.unstructured(header)); };
        if loop_shape.exception_body != Some(shape.body)
            || loop_shape.exit != Some(plan.loop_exit)
            || !shape.catches.is_empty()
            || region.label_scope().is_some()
            || region.exception_arm.is_some()
            || !self.layout.inside(plan.target, region)
        {
            return Err(self.unstructured(header));
        }
        self.require_empty_stack(machine, header)?;
        let scope = Scope {
            head: header,
            tail: plan.loop_exit,
            join: plan.target,
            name: format!("label{}", self.offset(plan.target)),
            edges: Edges::Finally { body: shape.body, entry: plan.entry, jump: plan.jump },
            exits: RefCell::new(Vec::with_capacity(2)),
        };
        let label_region = region.label_body(&scope, Some(plan.target));
        let start = self.lines.len();
        self.syntax(depth, &format!("{}: {{", scope.name));
        self.lines[start].sequence_boundary = true;
        // This plan already proved the separate latch and abrupt ordinary
        // exit, so emit the post-test loop without a speculative retry.
        self.emit_post_test_loop(header, test, label_region, machine, depth + 1)?;
        if self.region(plan.loop_exit, label_region, &mut machine.clone(), depth + 1)? {
            return Err(self.unstructured(plan.loop_exit));
        }
        let states = scope.exits.into_inner();
        let [prior, cleanup] = states.as_slice() else { return Err(self.unstructured(header)); };
        if prior.block != plan.entry || cleanup.block != finally.block() {
            return Err(self.unstructured(header));
        }
        let mut declarations = Vec::with_capacity(plan.locals.len());
        for local in &plan.locals {
            let offset = self.instructions[local.store].offset;
            let mut lines = self.lines[start..].iter_mut().filter(|line| line.offsets.contains(&offset));
            let (Some(line), None) = (lines.next(), lines.next()) else {
                return Err(StructureError::Flow { offset });
            };
            let source = if local.from_finally { &cleanup.state } else { &prior.state };
            let declaration = machine.promote_label_local(source, local.slot, &mut line.text)
                .ok_or(StructureError::Flow { offset })?;
            declarations.push(Line::new(depth, declaration, Vec::new()));
        }
        self.lines.splice(start..start, declarations);
        self.syntax(depth, "}");
        Ok(Some(plan.target))
    }

    pub(super) fn record_finally_label_break<'a, 'c>(
        &mut self,
        block: usize,
        region: Region<'_, 'a, 'c>,
        machine: &Machine<'a, 'c>,
        depth: usize,
        offsets: &mut Vec<u32>,
    ) -> Result<bool, StructureError> {
        let Some(scope) = region.label_scope() else { return Ok(false); };
        if let &Edges::Finally { body, entry, jump } = &scope.edges
            && region.exception_arm == Some(body)
            && block == entry
        {
            self.require_empty_stack(machine, block)?;
            scope.exits.borrow_mut().push(Exit { block, state: machine.clone() });
            let op = &self.instructions[jump];
            offsets.extend(op.offset..op.offset + op.len);
            self.push(depth, format!("break {};", scope.name), mem::take(offsets));
            return Ok(true);
        }
        Ok(false)
    }

    pub(super) fn record_finally_label_completion<'a, 'c>(
        region: Region<'_, 'a, 'c>,
        body: ArmId,
        block: usize,
        machine: &Machine<'a, 'c>,
    ) {
        if let Some(scope) = region.label_scope()
            && matches!(&scope.edges, Edges::Finally { body: owner, .. } if *owner == body)
        {
            scope.exits.borrow_mut().push(Exit { block, state: machine.clone() });
        }
    }

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
        Some(Plan { tail, join, break_count, edges: Edges::Explicit })
    }

    fn labeled_plain_block(&self, block: usize, region: Region<'_, '_, '_>) -> bool {
        self.graph.blocks[block].exception_successors.is_empty()
            && self.labeled_region_block(block, region)
    }

    fn labeled_region_block(&self, block: usize, region: Region<'_, '_, '_>) -> bool {
        let node = &self.graph.blocks[block];
        self.exceptions.contains(region.exception_arm, block)
            && self.exceptions.at_start(region.exception_arm, block).is_none()
            && self.exceptions.bypass_cleanup(block) == block
            && !self.exception_redirects.contains_key(&block)
            && self.layout.loops[block].is_none()
            && node.exception_predecessors.is_empty()
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
        self.emit_labeled(head, region, machine, depth, Head::If(condition), offsets, control, plan)
    }

    pub(super) fn emit_switch_or_labeled<'a, 'c>(
        &mut self,
        head: usize,
        region: Region<'_, 'a, 'c>,
        machine: &mut Machine<'a, 'c>,
        depth: usize,
        selector: Document,
        offsets: &mut Vec<u32>,
        control: RangeInclusive<u32>,
    ) -> Result<Option<usize>, StructureError> {
        let plan = if machine.this_is_initialized() && machine.stack_is_empty() {
            self.labeled_resource_switch(head, region)
        } else {
            None
        };
        let Some(plan) = plan else {
            return self.emit_switch(head, region, machine, depth, selector, offsets, control, None);
        };
        self.emit_labeled(head, region, machine, depth, Head::Switch(selector), offsets, control, plan)
    }

    fn emit_labeled<'a, 'c>(
        &mut self,
        head: usize,
        region: Region<'_, 'a, 'c>,
        machine: &mut Machine<'a, 'c>,
        depth: usize,
        kind: Head,
        offsets: &mut Vec<u32>,
        control: RangeInclusive<u32>,
        plan: Plan,
    ) -> Result<Option<usize>, StructureError> {
        let scope = Scope {
            head,
            tail: plan.tail,
            join: plan.join,
            name: format!("label{}", self.offset(plan.join)),
            edges: plan.edges,
            exits: RefCell::new(Vec::with_capacity(plan.break_count)),
        };
        let label_region = region.label_body(&scope, Some(plan.join));
        let start = self.lines.len();
        let mut body = machine.clone();
        let next = match kind {
            Head::If(condition) => self.emit_if(head, label_region, &mut body, depth + 1, condition, None, offsets, control)?,
            Head::Switch(selector) => self.emit_switch(head, label_region, &mut body, depth + 1, selector, offsets, control, None)?,
        };
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

    pub(super) fn emit_try_with_monitor_departure<'a, 'c>(
        &mut self,
        shape: &ProtectedRegion,
        region: Region<'_, 'a, 'c>,
        machine: &Machine<'a, 'c>,
        depth: usize,
    ) -> Result<Option<bool>, StructureError> {
        if shape.catches.is_empty() || region.label_scope().is_some() || region.loop_header.is_some()
        {
            return Ok(None);
        }
        let mut departures = self.exceptions.children_of(shape.body).filter_map(|child| {
            let child = self.exceptions.region(child);
            let departure = child.monitor.as_ref()?.departure?;
            Some((child.body, departure))
        });
        let Some((arm, departure)) = departures.next() else {
            return Ok(None);
        };
        let join = shape.join.ok_or(StructureError::ExceptionHandlers)?;
        if departures.next().is_some() {
            return Err(self.unstructured(departure.source));
        }
        // The source break skips the rest of the try, so the bytecode must
        // reach its join with no other work or exception transfer.
        let mut target = departure.target;
        while target != join {
            let block = &self.graph.blocks[target];
            let &[next] = block.successors.as_slice() else {
                return Err(self.unstructured(target));
            };
            if next <= target
                || next > join
                || !self.labeled_region_block(target, region.exception(Some(join), shape.body, None))
                || block.instructions.len() != 1
                || self.explicit_jump(target, next).is_none()
            {
                return Err(self.unstructured(target));
            }
            target = next;
        }
        self.emit_monitor_departure_scope(shape, region, machine, depth, arm, departure, None)
    }

    pub(super) fn emit_monitor_with_finally_departure<'a, 'c>(
        &mut self,
        shape: &ProtectedRegion,
        acquisition: usize,
        region: Region<'_, 'a, 'c>,
        machine: &Machine<'a, 'c>,
        depth: usize,
    ) -> Result<Option<bool>, StructureError> {
        let mut departures = self.exceptions.children_of(shape.body).filter_map(|child| {
            let finally = self.exceptions.region(child).finally.as_ref()?;
            let branch = finally.branched()?;
            let exit = branch.monitor_exit.as_ref()?;
            (exit.acquisition == acquisition)
                .then_some((finally.arm, exit.edge, (branch.entry, finally.block())))
        });
        let Some((arm, edge, branch)) = departures.next() else {
            return Ok(None);
        };
        if region.label_scope().is_some()
            || departures.next().is_some()
            || shape.join != Some(edge.target)
        {
            return Err(self.unstructured(edge.source));
        }
        self.emit_monitor_departure_scope(shape, region, machine, depth, arm, edge, Some(branch))
    }

    fn emit_monitor_departure_scope<'a, 'c>(
        &mut self,
        shape: &ProtectedRegion,
        region: Region<'_, 'a, 'c>,
        machine: &Machine<'a, 'c>,
        depth: usize,
        arm: ArmId,
        departure: MonitorDeparture,
        branch: Option<(usize, usize)>,
    ) -> Result<Option<bool>, StructureError> {
        let join = shape.join.ok_or(StructureError::ExceptionHandlers)?;
        let (head, tail) = branch.unwrap_or((shape.start, join));
        let scope = Scope {
            head,
            tail,
            join,
            name: format!("label{}", self.offset(join)),
            edges: Edges::Monitor { arm, edge: departure, branch_tail: branch.is_some() },
            exits: RefCell::new(Vec::with_capacity(1)),
        };
        self.syntax(depth, &format!("{}: {{", scope.name));
        let body = region.exception(Some(join), shape.body, Some(machine));
        if !self.scoped_arm(shape.start, body.label_body(&scope, Some(join)), machine, depth + 1)? {
            return Err(self.unstructured(departure.source));
        }
        let mut exits = scope.exits.into_inner().into_iter();
        let Some(Exit { state, .. }) = exits.next() else {
            return Err(self.unstructured(departure.source));
        };
        if exits.next().is_some() {
            return Err(self.unstructured(departure.source));
        }
        Self::check_scope(state, machine, self.offset(join))?;
        self.syntax(depth, "}");
        Ok(Some(true))
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
        let Some(scope) = region.label_scope() else { return Ok(false); };
        let jump = match &scope.edges {
            Edges::Explicit if scope.join == to && block != scope.tail
                && self.labeled_plain_block(block, region) =>
            {
                Some(self.explicit_jump(block, to).ok_or_else(|| self.unstructured(block))?)
            }
            Edges::Resource { arm, abrupt_entries } if region.exception_arm == Some(*arm)
                && abrupt_entries.contains(&to) && self.labeled_region_block(block, region) =>
            {
                self.explicit_jump(block, to)
            }
            Edges::Monitor { arm, edge, .. }
                if region.exception_arm == Some(*arm) && (edge.source, edge.target) == (block, to) =>
            {
                let jump = self.explicit_jump(block, to).ok_or_else(|| self.unstructured(block))?;
                scope.exits.borrow_mut().push(Exit { block, state: machine.clone() });
                offsets.push(jump);
                self.push(depth, format!("break {};", scope.name), mem::take(offsets));
                return Ok(true);
            }
            _ => return Ok(false),
        };
        if block <= scope.head || block >= scope.tail {
            return Err(self.unstructured(block));
        }
        let mut exits = scope.exits.borrow_mut();
        let edge = exits.len();
        exits.push(Exit { block, state: machine.clone() });
        if let Some(line) = self.lines.get_mut(first_line) {
            line.labeled_edge = Some(EdgeLine::First(edge));
        }
        offsets.extend(jump);
        let mut line = Line::new(depth, format!("break {};", scope.name), mem::take(offsets));
        line.labeled_edge = Some(EdgeLine::Break(edge));
        self.lines.push(line);
        Ok(true)
    }
}

fn branch(opcode: u8) -> bool {
    matches!(opcode, 0x99..=0xa6 | 0xc6 | 0xc7)
}
