// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

pub(crate) mod assertions;
mod exception_emit;
#[cfg(test)]
mod exception_tests;
mod flow;
#[cfg(test)]
mod join_tests;
mod protected;
mod string_switch;
mod switch_expression;
#[cfg(test)]
mod tests;

use std::cell::{Cell, RefCell};
use std::collections::BTreeMap;
use std::mem;
use std::ops::{Range, RangeInclusive};

use thiserror::Error;

use crate::bytecode::{Instruction, Operand};
use crate::cfg::ControlFlowGraph;
use crate::classfile::ExceptionHandler;
use crate::lift::{Effect, LiftError, Machine};
use crate::source_text::Document;

use self::flow::{Layout, Loop, LoopScope, Region, Transfer, While};
use self::protected::Exceptions;
use self::switch_expression::CaseLabel;

#[derive(Debug)]
pub(crate) struct Line {
    pub depth: usize,
    pub text: Document,
    pub offsets: Vec<u32>,
    loop_break: Option<LoopBreak>,
}

impl Line {
    fn new(depth: usize, text: impl Into<Document>, offsets: Vec<u32>) -> Self {
        Self {
            depth,
            text: text.into(),
            offsets,
            loop_break: None,
        }
    }
}

#[derive(Debug)]
struct LoopBreak {
    header: usize,
    edge: usize,
}

#[derive(Debug, Error)]
pub(crate) enum StructureError {
    #[error(transparent)]
    Lift(#[from] LiftError),
    #[error("unsupported exception handling region")]
    ExceptionHandlers,
    #[error("cannot represent a proven Java assertion without moving side effects")]
    Assertion,
    #[error("unsupported control flow at bytecode offset {offset}")]
    Flow { offset: u32 },
    #[error("nonempty operand stack at control-flow boundary at bytecode offset {offset}")]
    StackJoin { offset: u32 },
    #[error(
        "incompatible local variables across control-flow boundary at bytecode offset {offset}"
    )]
    LocalJoin { offset: u32 },
    #[error("control-flow nesting exceeds the supported depth")]
    Nesting,
}

#[cfg(test)]
pub(crate) fn structure(
    instructions: &[Instruction],
    graph: &ControlFlowGraph,
    machine: Machine<'_, '_>,
) -> Result<Vec<Line>, StructureError> {
    structure_with_assertions(instructions, graph, machine, &[], None)
}

pub(crate) fn structure_with_handlers(
    instructions: &[Instruction],
    graph: &ControlFlowGraph,
    machine: Machine<'_, '_>,
    handlers: &[ExceptionHandler],
) -> Result<Vec<Line>, StructureError> {
    structure_with_assertions(instructions, graph, machine, handlers, None)
}

pub(crate) fn structure_with_assertions(
    instructions: &[Instruction],
    graph: &ControlFlowGraph,
    machine: Machine<'_, '_>,
    handlers: &[ExceptionHandler],
    assertions: Option<&assertions::Sites>,
) -> Result<Vec<Line>, StructureError> {
    if handlers.is_empty()
        && graph
            .blocks
            .iter()
            .any(|block| !block.exception_successors.is_empty())
    {
        return Err(StructureError::ExceptionHandlers);
    }
    let exceptions = Exceptions::new(instructions, graph, handlers)?;
    structure_regions(instructions, graph, machine, &exceptions, assertions)
}

fn structure_regions(
    instructions: &[Instruction],
    graph: &ControlFlowGraph,
    mut machine: Machine<'_, '_>,
    exceptions: &Exceptions,
    assertions: Option<&assertions::Sites>,
) -> Result<Vec<Line>, StructureError> {
    if graph.blocks.is_empty() {
        return Ok(Vec::new());
    }
    let mut emitter = Emitter {
        instructions,
        graph,
        layout: Layout::new(graph, instructions, assertions)?,
        exceptions,
        assertions,
        emitted: vec![false; graph.blocks.len()],
        lines: Vec::new(),
    };
    emitter.region(0, Region::METHOD, &mut machine, 0)?;
    if assertions.is_some_and(|sites| !sites.all_emitted(&emitter.emitted)) {
        return Err(StructureError::Assertion);
    }
    for (block, reachable) in graph.reachable().into_iter().enumerate() {
        if reachable && !emitter.emitted[block] {
            return Err(emitter.unstructured(block));
        }
    }
    Ok(emitter.lines)
}

struct Emitter<'a> {
    instructions: &'a [Instruction],
    graph: &'a ControlFlowGraph,
    layout: Layout,
    exceptions: &'a Exceptions,
    assertions: Option<&'a assertions::Sites>,
    emitted: Vec<bool>,
    lines: Vec<Line>,
}

struct Tail {
    effect: Effect,
    offsets: Vec<u32>,
    control: Option<RangeInclusive<u32>>,
}

struct Condition {
    taken: usize,
    fallthrough: usize,
    when_true: Document,
    when_false: Document,
}

struct Arm<'a, 'c> {
    exit: Option<Machine<'a, 'c>>,
    offsets: Vec<u32>,
    start: usize,
    end: usize,
}

impl Emitter<'_> {
    /// Emits a region once. True means a path completes normally at its stop;
    /// false means all paths terminate or transfer to an enclosing region.
    fn region<'a, 'c>(
        &mut self,
        block: usize,
        region: Region<'_, 'a, 'c>,
        machine: &mut Machine<'a, 'c>,
        depth: usize,
    ) -> Result<bool, StructureError> {
        self.region_with_offsets(block, region, machine, depth, &mut Vec::new())
    }

    fn region_with_offsets<'a, 'c>(
        &mut self,
        block: usize,
        region: Region<'_, 'a, 'c>,
        machine: &mut Machine<'a, 'c>,
        depth: usize,
        pending: &mut Vec<u32>,
    ) -> Result<bool, StructureError> {
        self.run_region(block, region, machine, depth, pending, false)
    }

    fn run_region<'a, 'c>(
        &mut self,
        mut block: usize,
        region: Region<'_, 'a, 'c>,
        machine: &mut Machine<'a, 'c>,
        depth: usize,
        pending: &mut Vec<u32>,
        mut enter_loop: bool,
    ) -> Result<bool, StructureError> {
        // Bytecode need not originate from Java, so recursion depth is not
        // constrained by the nesting limits of a source compiler.
        if depth > 128 {
            return Err(StructureError::Nesting);
        }
        loop {
            block = self.exceptions.bypass_cleanup(block);
            let first_header = mem::take(&mut enter_loop);
            if !first_header {
                if region.stop == Some(block) {
                    return Ok(true);
                }
                if let Some((scope, transfer)) = region.loop_transfer(block) {
                    self.emit_loop_transfer(
                        block, region, scope, transfer, machine, depth, pending,
                    )?;
                    return Ok(false);
                }
            }
            if (!first_header && !self.layout.inside(block, region))
                || !self.exceptions.contains(region.exception_arm, block)
                || self.emitted[block]
            {
                return Err(self.unstructured(block));
            }
            if !first_header && let Some(id) = self.exceptions.at_start(region.exception_arm, block)
            {
                let Some(next) = self.emit_exception(id, region, machine, depth, pending)? else {
                    return Ok(false);
                };
                block = next;
                continue;
            }
            if !first_header && let Some(loop_shape) = self.layout.loops[block] {
                if !machine.this_is_initialized() {
                    return Err(self.unstructured(block));
                }
                let Some(exit) =
                    self.emit_loop(block, loop_shape, region, machine, depth, pending)?
                else {
                    return Ok(false);
                };
                block = exit;
                continue;
            }
            if let Some(next) =
                self.try_emit_string_switch(block, region, machine, depth, pending)?
            {
                let Some(next) = next else { return Ok(false) };
                block = next;
                continue;
            }
            self.emitted[block] = true;
            let Tail {
                effect,
                mut offsets,
                control,
            } = self.lift_block(block, machine, region, depth, mem::take(pending))?;
            match effect {
                Effect::None => {
                    block = self.single_successor(block)?;
                    *pending = offsets;
                }
                Effect::Jump(target) => {
                    let next = self.single_successor(block)?;
                    if self.graph.block_at(target) != Some(next) {
                        return Err(self.unstructured(block));
                    }
                    block = next;
                    *pending = offsets;
                }
                Effect::Branch {
                    target,
                    when_true,
                    when_false,
                } => {
                    let (taken, fallthrough) = self.branch_targets(block, target)?;
                    let condition = Condition {
                        taken,
                        fallthrough,
                        when_true,
                        when_false,
                    };
                    let control = control.expect("conditional control schedule");
                    let Some(next) = self.emit_if(
                        block,
                        region,
                        machine,
                        depth,
                        condition,
                        &mut offsets,
                        control,
                    )?
                    else {
                        return Ok(false);
                    };
                    block = next;
                    *pending = offsets;
                }
                Effect::Switch { selector } => {
                    let control = control.expect("switch control schedule");
                    let Some(next) = self.emit_switch(
                        block,
                        region,
                        machine,
                        depth,
                        selector,
                        &mut offsets,
                        control,
                        None,
                    )?
                    else {
                        return Ok(false);
                    };
                    block = next;
                    *pending = offsets;
                }
                Effect::Return(value) => {
                    let text = value.map_or_else(
                        || Document::from("return;"),
                        |value| surrounded(value, "return ", ";"),
                    );
                    self.push(depth, text, offsets);
                    return Ok(false);
                }
                Effect::Throw(value) => {
                    self.push(depth, surrounded(value, "throw ", ";"), offsets);
                    return Ok(false);
                }
                Effect::Statement(_) | Effect::FieldAssignment { .. } => {
                    return Err(self.unstructured(block));
                }
            }
        }
    }

    fn lift_block<'a, 'c>(
        &mut self,
        block: usize,
        machine: &mut Machine<'a, 'c>,
        region: Region<'_, 'a, 'c>,
        depth: usize,
        offsets: Vec<u32>,
    ) -> Result<Tail, StructureError> {
        let mut range = self.graph.blocks[block].instructions.clone();
        self.exception_range(block, region, &mut range)?;
        self.lift_range(block, range, machine, region, depth, offsets)
    }

    fn lift_range<'a, 'c>(
        &mut self,
        block: usize,
        range: Range<usize>,
        machine: &mut Machine<'a, 'c>,
        region: Region<'_, 'a, 'c>,
        depth: usize,
        mut offsets: Vec<u32>,
    ) -> Result<Tail, StructureError> {
        let mut tail = Effect::None;
        let mut control = None;
        let mut index = range.start;
        while index < range.end {
            if self.exceptions.skips_instruction(index) {
                index += 1;
                continue;
            }
            let instruction = &self.instructions[index];
            if matches!(instruction.opcode, 0xbc | 0xbd)
                && let Some(consumed) = machine
                    .try_array_initializer(&self.instructions[index..range.end], |relative, _| {
                        !self.exceptions.skips_instruction(index + relative)
                    })
            {
                offsets.extend(
                    self.instructions[index..index + consumed]
                        .iter()
                        .filter(|op| op.opcode != 0)
                        .flat_map(|op| op.offset..op.offset + op.len),
                );
                index += consumed;
                continue;
            }
            if index + 1 == range.end {
                control = machine.control_order(instruction)?;
            }
            let effect = machine.step(instruction)?;
            if let Some(baseline) = region.protected
                && matches!(instruction.opcode, 0x36..=0x4e)
                && !machine.keeps_locals_of(baseline)
            {
                return Err(StructureError::LocalJoin {
                    offset: instruction.offset,
                });
            }
            let prelude = machine.take_prelude();
            if machine.instruction_has_source()
                && (!prelude.is_empty() || !matches!(effect, Effect::Jump(_)))
            {
                offsets.extend(instruction.offset..instruction.offset + instruction.len);
            }
            for statement in prelude {
                self.push(depth, statement, mem::take(&mut offsets));
            }
            match effect {
                Effect::None => {}
                Effect::Statement(statement) => {
                    self.push(depth, statement, mem::take(&mut offsets))
                }
                Effect::FieldAssignment { mut target, value } => {
                    target.push_str(" = ");
                    target.append(value);
                    target.push(';');
                    self.push(depth, target, mem::take(&mut offsets));
                }
                transfer if index + 1 == range.end => tail = transfer,
                _ => return Err(self.unstructured(block)),
            }
            index += 1;
        }
        Ok(Tail {
            effect: tail,
            offsets,
            control,
        })
    }

    fn emit_if<'a, 'c>(
        &mut self,
        block: usize,
        region: Region<'_, 'a, 'c>,
        machine: &mut Machine<'a, 'c>,
        depth: usize,
        mut condition: Condition,
        offsets: &mut Vec<u32>,
        mut control: RangeInclusive<u32>,
    ) -> Result<Option<usize>, StructureError> {
        if self.assertion_starts(block) {
            return self.emit_assertion(block, region, machine, depth, offsets);
        }
        let held = machine.hold_control_stack(&control)?;
        let prelude = machine.take_prelude();
        self.collapse_condition(
            block,
            region,
            machine,
            depth,
            &mut condition,
            offsets,
            &mut control,
        )?;
        let Condition {
            taken,
            fallthrough,
            when_true,
            when_false,
        } = condition;
        if taken == fallthrough {
            if machine.has_uninitialized_stack() {
                return Err(self.unstructured(block));
            }
            for statement in prelude {
                self.push(depth, statement, mem::take(offsets));
            }
            // Even a degenerate condition can evaluate a call or throw.
            self.push(
                depth,
                surrounded(when_false, "if (", ") {"),
                mem::take(offsets),
            );
            self.syntax(depth, "}");
            return Ok(Some(taken));
        }
        let join = self
            .layout
            .normal_join(block, region)
            .or_else(|| {
                self.layout
                    .common_join(self.graph, region, [(fallthrough, None), (taken, None)])
            })
            .or_else(|| {
                let abrupt = |arm| self.is_terminal(arm) || region.loop_transfer(arm).is_some();
                let next = match (abrupt(taken), abrupt(fallthrough)) {
                    (true, false) => fallthrough,
                    (false, true) => taken,
                    _ => return None,
                };
                (region.stop == Some(next) || self.layout.inside(next, region)).then_some(next)
            })
            .or(region.stop);
        let arm_region = region.branch(join);
        let (then_at, else_at, condition, inverse) = if join == Some(fallthrough) {
            (taken, fallthrough, when_true, when_false)
        } else {
            (fallthrough, taken, when_false, when_true)
        };

        let start = self.lines.len();
        let then = self.branch_arm(then_at, arm_region, machine, depth + 1)?;
        let otherwise = self.branch_arm(else_at, arm_region, machine, depth + 1)?;
        if start == otherwise.end
            && let (Some(yes), Some(no)) = (&then.exit, &otherwise.exit)
            && yes.same_locals(machine)
            && no.same_locals(machine)
            && let Some(restored) =
                machine.merge_conditional_stack(yes, no, &condition, &inverse, &control, held)?
        {
            if !restored {
                for statement in prelude {
                    self.push(depth, statement, mem::take(offsets));
                }
            }
            offsets.extend(then.offsets);
            offsets.extend(otherwise.offsets);
            return Ok(join);
        }
        if machine.has_uninitialized_stack() {
            return Err(self.unstructured(block));
        }

        let exits = [&then, &otherwise]
            .into_iter()
            .filter(|arm| arm.exit.is_some())
            .collect::<Vec<_>>();
        let (declarations, assignments) = if exits.is_empty() {
            (Vec::new(), Vec::new())
        } else {
            self.merge_arms(machine, join.expect("reached an if join"), &exits)?
        };
        let mut assignments = assignments.into_iter();
        let mut assignment_lines = |falls: bool, mut offsets: Vec<u32>| {
            falls
                .then(|| assignments.next().expect("one assignment list per arm"))
                .unwrap_or_default()
                .into_iter()
                .map(|text| Line::new(depth + 1, text, mem::take(&mut offsets)))
                .collect::<Vec<_>>()
        };
        let then_falls = then.exit.is_some();
        let else_falls = otherwise.exit.is_some();
        let then_end = then.end;
        let else_end = otherwise.end;
        let mut then_lines = assignment_lines(then_falls, then.offsets);
        let else_lines = assignment_lines(else_falls, otherwise.offsets);
        if join != Some(else_at) || !else_lines.is_empty() {
            self.lines.splice(else_end..else_end, else_lines);
            then_lines.push(Line::new(depth, "} else {", Vec::new()));
        }
        self.lines.splice(then_end..then_end, then_lines);
        let mut header = Vec::new();
        for statement in prelude {
            header.push(Line::new(depth, statement, mem::take(offsets)));
        }
        header.extend(
            declarations
                .into_iter()
                .map(|text| Line::new(depth, text, Vec::new())),
        );
        header.push(Line::new(
            depth,
            surrounded(condition, "if (", ") {"),
            mem::take(offsets),
        ));
        self.lines.splice(start..start, header);
        self.syntax(depth, "}");
        Ok(if then_falls || else_falls { join } else { None })
    }

    fn collapse_condition<'a, 'c>(
        &mut self,
        mut head: usize,
        region: Region<'_, 'a, 'c>,
        machine: &Machine<'a, 'c>,
        depth: usize,
        condition: &mut Condition,
        offsets: &mut Vec<u32>,
        control: &mut RangeInclusive<u32>,
    ) -> Result<(), StructureError> {
        while condition.taken != condition.fallthrough {
            let candidate = [
                (condition.fallthrough, condition.taken),
                (condition.taken, condition.fallthrough),
            ]
            .into_iter()
            .find(|&(next, shared)| {
                let node = &self.graph.blocks[next];
                node.predecessors.as_slice() == [head]
                    && node.successors.len() == 2
                    && node.successors.contains(&shared)
                    && !self.emitted[next]
                    && !self.assertion_starts(next)
                    && self.layout.loops[next].is_none()
                    && self.layout.inside(next, region)
                    && region.exception_arm.is_none()
                    && self
                        .exceptions
                        .at_start(region.exception_arm, next)
                        .is_none()
            });
            let Some((next, shared)) = candidate else {
                break;
            };
            let start = self.lines.len();
            let mut along = machine.clone();
            // A candidate must compute only the next condition. In
            // particular it may not run a statement on the shared arm's path.
            let tail = self.lift_block(next, &mut along, region, depth, Vec::new());
            if self.lines.len() != start {
                self.lines.truncate(start);
                break;
            }
            let Ok(Tail {
                effect:
                    Effect::Branch {
                        target,
                        when_true,
                        when_false,
                    },
                offsets: inner_offsets,
                control: Some(inner_control),
            }) = tail
            else {
                break;
            };
            if !along.same_locals(machine)
                || !along.same_control_stack(machine)
                || *inner_control.start() <= *control.end()
            {
                break;
            }
            let (taken, fallthrough) = self.branch_targets(next, target)?;
            let (unique, succeeds, fails) = if taken == shared {
                (fallthrough, when_false, when_true)
            } else {
                (taken, when_true, when_false)
            };
            if next == condition.taken {
                condition.taken = unique;
                condition.when_true = logical(mem::take(&mut condition.when_true), "&&", succeeds);
                condition.when_false = logical(mem::take(&mut condition.when_false), "||", fails);
            } else {
                condition.fallthrough = unique;
                condition.when_false =
                    logical(mem::take(&mut condition.when_false), "&&", succeeds);
                condition.when_true = logical(mem::take(&mut condition.when_true), "||", fails);
            }
            self.emitted[next] = true;
            head = next;
            offsets.extend(inner_offsets);
            *control = *control.start()..=*inner_control.end();
        }
        Ok(())
    }

    fn emit_loop_test<'a, 'c>(
        &mut self,
        scope: &LoopScope<'a, 'c>,
        test: While,
        region: Region<'_, 'a, 'c>,
        iteration: &mut Machine<'a, 'c>,
        depth: usize,
    ) -> Result<(usize, usize, Document), StructureError> {
        let header = scope.header;
        self.emitted[header] = true;
        let Tail {
            effect,
            mut offsets,
            control,
        } = self.lift_block(header, iteration, region, depth, Vec::new())?;
        let Effect::Branch {
            target,
            when_true,
            when_false,
        } = effect
        else {
            return Err(self.unstructured(header));
        };
        let (taken, fallthrough) = self.branch_targets(header, target)?;
        if !matches!((taken, fallthrough), (a, b)
            if (a == test.body && b == test.exit) || (a == test.exit && b == test.body))
        {
            return Err(self.unstructured(header));
        }
        let mut control = control.expect("loop condition schedule");
        iteration.freeze_control_stack(&control)?;
        for statement in iteration.take_prelude() {
            self.push(depth, statement, mem::take(&mut offsets));
        }
        let mut condition = Condition {
            taken,
            fallthrough,
            when_true,
            when_false,
        };
        self.collapse_condition(
            header,
            region,
            iteration,
            depth,
            &mut condition,
            &mut offsets,
            &mut control,
        )?;
        let (body, condition, exit_condition) = if condition.taken == test.exit {
            (
                condition.fallthrough,
                condition.when_false,
                condition.when_true,
            )
        } else if condition.fallthrough == test.exit {
            (condition.taken, condition.when_true, condition.when_false)
        } else {
            return Err(self.unstructured(header));
        };
        let guard = self.lines.len();
        self.push(depth, surrounded(exit_condition, "if (", ") {"), offsets);
        self.emit_loop_transfer(
            test.exit,
            region,
            scope,
            Transfer::Break,
            iteration,
            depth + 1,
            &mut Vec::new(),
        )?;
        self.syntax(depth, "}");
        Ok((body, guard, condition))
    }

    fn emit_loop<'a, 'c>(
        &mut self,
        header: usize,
        shape: Loop,
        region: Region<'_, 'a, 'c>,
        machine: &mut Machine<'a, 'c>,
        depth: usize,
        pending: &mut Vec<u32>,
    ) -> Result<Option<usize>, StructureError> {
        for statement in machine.bind_edge_stack(self.offset(header), None)? {
            self.push(depth, statement, mem::take(pending));
        }
        pending.clear();
        let scope = Self::loop_scope(header, shape.exit, region, machine);
        let head_line = self.lines.len();
        self.syntax(depth, "while (true) {");
        let mut iteration = machine.clone();
        let body_region = region.loop_body(&scope);
        let (repeats, guard) = if let Some(test) = shape.test {
            let (body, guard, condition) =
                self.emit_loop_test(&scope, test, body_region, &mut iteration, depth + 1)?;
            let repeats =
                self.region_with_offsets(body, body_region, &mut iteration, depth + 1, pending)?;
            (repeats, Some((guard, condition)))
        } else {
            (
                self.run_region(
                    header,
                    body_region,
                    &mut iteration,
                    depth + 1,
                    pending,
                    true,
                )?,
                None,
            )
        };
        if repeats {
            self.emit_backedge(&scope, &iteration, depth + 1, pending)?;
        }
        pending.clear();
        self.syntax(depth, "}");

        let breaks = scope.breaks.borrow();
        let Some(exit) = shape.exit.filter(|_| !breaks.is_empty()) else {
            self.label_loop(head_line, &scope);
            return Ok(None);
        };
        let exits = breaks.iter().collect::<Vec<_>>();
        let offset = self.offset(exit);
        let stack = machine.merge_stack(&exits, offset)?;
        let locals = machine.merge_locals(&exits, offset, |slot| self.local_is_live(exit, slot))?;
        let mut assignments = stack
            .arms
            .into_iter()
            .zip(locals.arms)
            .map(|(mut stack, locals)| {
                stack.extend(locals.into_iter().map(|copy| copy.statement));
                stack
            })
            .collect::<Vec<_>>();
        if let Some((guard_line, condition)) = guard
            && guard_line == head_line + 1
            && assignments[0].is_empty()
        {
            let offsets = mem::take(&mut self.lines[guard_line].offsets);
            self.lines[head_line] =
                Line::new(depth, surrounded(condition, "while (", ") {"), offsets);
            self.lines.drain(guard_line..guard_line + 3);
        }
        self.label_loop(head_line, &scope);
        if assignments.iter().any(|edge| !edge.is_empty()) {
            let body = self.lines.split_off(head_line + 1);
            for mut line in body {
                if line
                    .loop_break
                    .as_ref()
                    .is_some_and(|edge| edge.header == header)
                {
                    let edge = line.loop_break.take().unwrap();
                    for statement in mem::take(&mut assignments[edge.edge]) {
                        self.push(line.depth, statement, mem::take(&mut line.offsets));
                    }
                }
                self.lines.push(line);
            }
        } else {
            for line in &mut self.lines[head_line + 1..] {
                if line
                    .loop_break
                    .as_ref()
                    .is_some_and(|edge| edge.header == header)
                {
                    line.loop_break = None;
                }
            }
        }
        self.lines.splice(
            head_line..head_line,
            stack
                .declarations
                .into_iter()
                .chain(locals.declarations)
                .map(|text| Line::new(depth, text, Vec::new())),
        );
        Ok(Some(exit))
    }

    fn loop_scope<'a, 'c>(
        header: usize,
        exit: Option<usize>,
        region: Region<'_, 'a, 'c>,
        machine: &Machine<'a, 'c>,
    ) -> LoopScope<'a, 'c> {
        LoopScope {
            header,
            exit,
            entry: machine.clone(),
            breaks: RefCell::default(),
            labeled: Cell::new(false),
            switch_depth: region.switch_depth,
            exception_arm: region.exception_arm,
        }
    }

    fn label_loop(&mut self, line: usize, scope: &LoopScope<'_, '_>) {
        if scope.labeled.get() {
            let label = format!("label{}: ", self.offset(scope.header));
            self.lines[line].text.insert_str(0, &label);
        }
    }

    fn emit_backedge<'a, 'c>(
        &mut self,
        scope: &LoopScope<'a, 'c>,
        machine: &Machine<'a, 'c>,
        depth: usize,
        offsets: &mut Vec<u32>,
    ) -> Result<(), StructureError> {
        let stack = machine.update_edge_stack(&scope.entry, self.offset(scope.header))?;
        let locals = machine
            .update_edge_locals(&scope.entry, |slot| self.local_is_live(scope.header, slot))?;
        for statement in stack.into_iter().chain(locals) {
            self.push(depth, statement, mem::take(offsets));
        }
        Ok(())
    }

    fn emit_loop_transfer<'a, 'c>(
        &mut self,
        target: usize,
        region: Region<'_, 'a, 'c>,
        scope: &LoopScope<'a, 'c>,
        transfer: Transfer,
        machine: &Machine<'a, 'c>,
        depth: usize,
        offsets: &mut Vec<u32>,
    ) -> Result<(), StructureError> {
        if region.exception_arm != scope.exception_arm {
            return Err(self.unstructured(target));
        }
        let label = region.loop_header != Some(scope.header)
            || (transfer == Transfer::Break && region.switch_depth > scope.switch_depth);
        let keyword = match transfer {
            Transfer::Continue => "continue",
            Transfer::Break => "break",
        };
        let text = if label {
            scope.labeled.set(true);
            format!("{keyword} label{};", self.offset(scope.header))
        } else {
            format!("{keyword};")
        };
        match transfer {
            Transfer::Continue => {
                self.emit_backedge(scope, machine, depth, offsets)?;
                self.push(depth, text, mem::take(offsets));
            }
            Transfer::Break => {
                let mut states = scope.breaks.borrow_mut();
                let edge = states.len();
                states.push(machine.clone());
                let mut line = Line::new(depth, text, mem::take(offsets));
                line.loop_break = Some(LoopBreak {
                    header: scope.header,
                    edge,
                });
                self.lines.push(line);
            }
        }
        Ok(())
    }

    fn emit_switch<'a, 'c>(
        &mut self,
        block: usize,
        region: Region<'_, 'a, 'c>,
        machine: &mut Machine<'a, 'c>,
        depth: usize,
        selector: Document,
        offsets: &mut Vec<u32>,
        control: RangeInclusive<u32>,
        dispatch: Option<&string_switch::Dispatch>,
    ) -> Result<Option<usize>, StructureError> {
        let instruction = &self.instructions[self.graph.blocks[block].instructions.end - 1];
        let (default, cases) = match dispatch {
            Some(dispatch) => (dispatch.default, dispatch.cases.as_slice()),
            None => match &instruction.operand {
                Operand::Switch { default, cases } => (*default, cases.as_slice()),
                _ => return Err(self.unstructured(block)),
            },
        };
        let default = self
            .graph
            .block_at(default)
            .ok_or_else(|| self.unstructured(block))?;
        let mut groups = BTreeMap::<usize, Vec<CaseLabel>>::new();
        groups.entry(default).or_default();
        for &(key, target) in cases {
            let target = self
                .graph
                .block_at(target)
                .ok_or_else(|| self.unstructured(block))?;
            // tableswitch pads missing keys with the default target.
            if target != default || dispatch.is_some() {
                let (text, offsets) = if let Some(dispatch) = dispatch {
                    let (text, offsets) = dispatch.label(key);
                    (text.to_owned(), offsets)
                } else {
                    let text = machine
                        .enum_switch_label(instruction.offset, key)
                        .map_or_else(|| key.to_string(), str::to_owned);
                    (text, Vec::new())
                };
                groups
                    .entry(target)
                    .or_default()
                    .push(CaseLabel { text, offsets });
            }
        }
        let join = self
            .layout
            .normal_join(block, region)
            .or_else(|| {
                let mut targets = groups.keys().copied().peekable();
                let arms = std::iter::from_fn(|| {
                    let target = targets.next()?;
                    let fallthrough = targets
                        .peek()
                        .copied()
                        .filter(|&next| self.layout.can_fall_through(target, next, None));
                    Some((target, fallthrough))
                });
                self.layout.common_join(self.graph, region, arms)
            })
            .or(region.stop);
        if let Some(join) = join
            && self.try_switch_expression(
                block, region, machine, depth, &selector, &groups, default, join, &control,
            )
        {
            return Ok(Some(join));
        }
        if machine.has_uninitialized_stack() {
            return Err(self.unstructured(block));
        }
        let switch_region = region.switch_body(join);
        let has_fallthrough = || {
            let targets = groups.keys().copied();
            targets
                .clone()
                .zip(targets.skip(1))
                .any(|(target, next)| self.layout.can_fall_through(target, next, join))
        };
        if !machine.stack_is_empty() && has_fallthrough() {
            for statement in machine.bind_edge_stack(self.offset(block), Some(*control.start()))? {
                self.push(depth, statement, mem::take(offsets));
            }
        } else {
            machine.freeze_control_stack(&control)?;
        }
        for statement in machine.take_prelude() {
            self.push(depth, statement, mem::take(offsets));
        }
        let start = self.lines.len();
        self.push(
            depth,
            surrounded(selector, "switch (", ") {"),
            mem::take(offsets),
        );
        let mut arms = Vec::new();
        let mut groups = groups.into_iter().peekable();
        while let Some((target, keys)) = groups.next() {
            let fallthrough = groups
                .peek()
                .map(|&(next, _)| next)
                .filter(|&next| self.layout.can_fall_through(target, next, join));
            let arm_region = if let Some(next) = fallthrough {
                switch_region.branch(Some(next))
            } else {
                switch_region
            };
            let mut keys = keys.into_iter().peekable();
            while let Some(CaseLabel { mut text, offsets }) = keys.next() {
                text.insert_str(0, "case ");
                text.push_str(if keys.peek().is_none() && target != default {
                    ": {"
                } else {
                    ":"
                });
                self.push(depth + 1, text, offsets);
            }
            if target == default {
                self.syntax(depth + 1, "default: {");
            }
            let arm = self.branch_arm(target, arm_region, machine, depth + 2)?;
            if let Some(end) = &arm.exit {
                if let Some(next) = fallthrough {
                    let mut offsets = arm.offsets;
                    for statement in end.update_edge_stack(machine, self.offset(next))? {
                        self.push(depth + 2, statement, mem::take(&mut offsets));
                    }
                    let updates =
                        end.update_edge_locals(machine, |slot| self.local_is_live(next, slot))?;
                    for statement in updates {
                        self.push(depth + 2, statement, mem::take(&mut offsets));
                    }
                } else {
                    arms.push(arm);
                    self.syntax(depth + 2, "break;");
                }
            }
            self.syntax(depth + 1, "}");
        }
        self.syntax(depth, "}");
        if arms.is_empty() {
            return Ok(None);
        }
        let join = join.expect("reached a switch join");
        let exits = arms.iter().collect::<Vec<_>>();
        let (declarations, assignments) = self.merge_arms(machine, join, &exits)?;
        for (arm, assignments) in arms.into_iter().zip(assignments).rev() {
            let mut offsets = arm.offsets;
            self.lines.splice(
                arm.end..arm.end,
                assignments
                    .into_iter()
                    .map(|text| Line::new(depth + 2, text, mem::take(&mut offsets))),
            );
        }
        self.lines.splice(
            start..start,
            declarations
                .into_iter()
                .map(|text| Line::new(depth, text, Vec::new())),
        );
        Ok(Some(join))
    }

    fn branch_arm<'a, 'c>(
        &mut self,
        start: usize,
        region: Region<'_, 'a, 'c>,
        baseline: &Machine<'a, 'c>,
        depth: usize,
    ) -> Result<Arm<'a, 'c>, StructureError> {
        let start_line = self.lines.len();
        let mut arm = baseline.clone();
        let mut offsets = Vec::new();
        let reaches = self.region_with_offsets(start, region, &mut arm, depth, &mut offsets)?;
        Ok(Arm {
            exit: reaches.then_some(arm),
            offsets,
            start: start_line,
            end: self.lines.len(),
        })
    }

    fn merge_arms<'a, 'c>(
        &mut self,
        machine: &mut Machine<'a, 'c>,
        join: usize,
        arms: &[&Arm<'a, 'c>],
    ) -> Result<(Vec<Document>, Vec<Vec<Document>>), StructureError> {
        let offset = self.offset(join);
        let exits = arms
            .iter()
            .map(|arm| arm.exit.as_ref().expect("arm reached the join"))
            .collect::<Vec<_>>();
        let mut code = machine.merge_stack(&exits, offset)?;
        let locals = machine.merge_locals(&exits, offset, |slot| self.local_is_live(join, slot))?;
        code.declarations.extend(locals.declarations);
        for ((arm, stack), locals) in arms.iter().zip(&mut code.arms).zip(locals.arms) {
            let mut last = (stack.is_empty() && arm.start < arm.end)
                .then(|| &mut self.lines[arm.end - 1].text);
            for copy in locals {
                if !last.as_deref_mut().is_some_and(|line| copy.fuse(line)) {
                    stack.push(copy.statement);
                }
            }
        }
        Ok((code.declarations, code.arms))
    }

    fn local_is_live(&mut self, block: usize, slot: u16) -> bool {
        self.layout
            .local_is_live(self.graph, self.instructions, block, slot)
    }

    fn require_empty_stack(
        &self,
        machine: &Machine<'_, '_>,
        block: usize,
    ) -> Result<(), StructureError> {
        if machine.stack_is_empty() {
            Ok(())
        } else {
            Err(StructureError::StackJoin {
                offset: self.offset(block),
            })
        }
    }
    fn scoped_arm<'a, 'c>(
        &mut self,
        start: usize,
        region: Region<'_, 'a, 'c>,
        baseline: &Machine<'a, 'c>,
        depth: usize,
    ) -> Result<bool, StructureError> {
        if region.stop == Some(start) {
            return Ok(true);
        }
        let mut arm = baseline.clone();
        let reaches = self.region(start, region, &mut arm, depth)?;
        if reaches {
            Self::check_scope(
                arm,
                baseline,
                self.offset(region.stop.expect("reached a region stop")),
            )?;
        }
        Ok(reaches)
    }

    fn check_scope<'a, 'c>(
        mut end: Machine<'a, 'c>,
        baseline: &Machine<'a, 'c>,
        offset: u32,
    ) -> Result<(), StructureError> {
        if !end.stack_is_empty() || !baseline.stack_is_empty() {
            return Err(StructureError::StackJoin { offset });
        }
        if !end.same_locals(baseline) && !end.discard_branch_locals(baseline) {
            return Err(StructureError::LocalJoin { offset });
        }
        Ok(())
    }

    fn is_terminal(&self, block: usize) -> bool {
        self.graph.blocks[block].successors.is_empty()
    }

    fn single_successor(&self, block: usize) -> Result<usize, StructureError> {
        match self.graph.blocks[block].successors.as_slice() {
            &[next] => Ok(next),
            _ => Err(self.unstructured(block)),
        }
    }

    fn branch_targets(&self, block: usize, target: u32) -> Result<(usize, usize), StructureError> {
        let taken = self
            .graph
            .block_at(target)
            .ok_or_else(|| self.unstructured(block))?;
        match *self.graph.blocks[block].successors.as_slice() {
            [first, next] if first == taken => Ok((taken, next)),
            [only] if only == taken => Ok((taken, taken)),
            _ => Err(self.unstructured(block)),
        }
    }

    fn offset(&self, block: usize) -> u32 {
        self.instructions[self.graph.blocks[block].instructions.start].offset
    }

    fn unstructured(&self, block: usize) -> StructureError {
        StructureError::Flow {
            offset: self.offset(block),
        }
    }

    fn push(&mut self, depth: usize, text: impl Into<Document>, offsets: Vec<u32>) {
        self.lines.push(Line::new(depth, text, offsets));
    }

    fn syntax(&mut self, depth: usize, text: &str) {
        self.push(depth, text, Vec::new());
    }
}

fn surrounded(mut text: Document, prefix: &str, suffix: &str) -> Document {
    text.surround(prefix, suffix);
    text
}

fn logical(mut left: Document, op: &str, mut right: Document) -> Document {
    for text in [&mut left, &mut right] {
        if text.contains('?') || (op == "&&" && text.contains(" || ")) {
            text.surround("(", ")");
        }
    }
    left.push(' ');
    left.push_str(op);
    left.push(' ');
    left.append(right);
    left
}
