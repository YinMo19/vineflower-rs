// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

pub(crate) mod assertions;
mod boolean_returns;
mod decision_graph;
mod do_while;
mod exception_emit;
mod flow;
mod for_loops;
mod instanceof_patterns;
mod irreducible;
mod labeled_blocks;
mod local_joins;
mod numeric_switch;
mod pattern_record;
mod pattern_switch;
mod protected;
mod string_switch;
mod switch_exit;
mod switch_expression;

use std::cell::{Cell, RefCell};
use std::collections::BTreeMap;
use std::mem;
use std::ops::{Range, RangeInclusive};

use thiserror::Error;

use crate::bytecode::{Instruction, Operand};
use crate::cfg::ControlFlowGraph;
use crate::classfile::ExceptionHandler;
use crate::lift::{BooleanCondition, Effect, LiftError, Machine};
use crate::source_text::{Document, Infix};

use self::boolean_returns::BooleanReturn;
use self::exception_emit::ExceptionRedirect;
use self::flow::{Layout, Loop, LoopScope, Region, Transfer, While};
use self::protected::Exceptions;
use self::switch_expression::CaseLabel;
pub(crate) use self::switch_expression::enum_argument_switch;

#[derive(Debug)]
pub(crate) struct Line {
    pub depth: usize,
    pub text: Document,
    pub offsets: Vec<u32>,
    pub sequence_boundary: bool,
    loop_break: Option<LoopBreak>,
    switch_break: Option<usize>,
    labeled_edge: Option<labeled_blocks::EdgeLine>,
    predicate_edge: Option<switch_expression::predicate::Edge>,
    boolean_return: Option<BooleanReturn>,
    detached_declaration: bool,
}

impl Line {
    fn new(depth: usize, text: impl Into<Document>, offsets: Vec<u32>) -> Self {
        Self {
            depth,
            text: text.into(),
            offsets,
            sequence_boundary: false,
            loop_break: None,
            switch_break: None,
            labeled_edge: None,
            predicate_edge: None,
            boolean_return: None,
            detached_declaration: false,
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
    mut machine: Machine<'_, '_>,
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
    if assertions.is_none()
        && let Some((projected, graph, plans)) =
            pattern_record::Plans::prove(instructions, graph, handlers, &mut machine)
    {
        return structure_regions(&projected, &graph, machine, &[], None, Some(&plans));
    }
    if handlers.is_empty()
        && assertions.is_none()
        && let Some(result) = boolean_returns::structure_with_boolean_tails(instructions, graph, &mut machine)
    {
        return result;
    }
    structure_regions(instructions, graph, machine, handlers, assertions, None)
}

fn structure_regions(
    instructions: &[Instruction],
    graph: &ControlFlowGraph,
    mut machine: Machine<'_, '_>,
    handlers: &[ExceptionHandler],
    assertions: Option<&assertions::Sites>,
    record_patterns: Option<&pattern_record::Plans>,
) -> Result<Vec<Line>, StructureError> {
    let exceptions = Exceptions::new(instructions, graph, handlers, Some(&machine))?;
    if graph.blocks.is_empty() {
        if !machine.this_is_initialized() {
            return Err(StructureError::Flow { offset: 0 });
        }
        return Ok(Vec::new());
    }
    if let [block] = graph.blocks.as_slice()
        && block.successors.is_empty()
        && block.exception_successors.is_empty()
    {
        machine.track_straight_line_ints();
    }
    let layout = Layout::with_exceptions(graph, instructions, assertions, &exceptions).or_else(|error| {
        if machine.supports_switch_expressions() {
            switch_expression::predicate::loop_layout(graph, instructions, assertions, &exceptions, error)
        } else {
            Err(error)
        }
    })?;
    let mut emitter = Emitter {
        instructions,
        graph,
        layout,
        exceptions: &exceptions,
        exception_redirects: BTreeMap::new(),
        resource_epilogue: None,
        assertions,
        record_patterns,
        cycle_rollout: None,
        emitted: vec![false; graph.blocks.len()],
        lines: Vec::new(),
    };
    for block in exceptions.synthetic_handler_blocks() {
        emitter.emitted[block] = true;
    }
    if handlers.is_empty()
        && assertions.is_none()
        && record_patterns.is_none()
        && let Some(cycle) = irreducible::Cycle::prove(instructions, graph, &emitter.layout)
    {
        emitter.emit_irreducible_cycle(cycle, &mut machine)?;
    } else {
        emitter.region(0, Region::METHOD, &mut machine, 0)?;
    }
    if !machine.this_is_initialized() {
        return Err(emitter.unstructured(0));
    }
    if assertions.is_some_and(|sites| !sites.all_emitted(&emitter.emitted)) {
        return Err(StructureError::Assertion);
    }
    for (block, reachable) in graph.reachable().into_iter().enumerate() {
        if reachable && !emitter.emitted[block] {
            return Err(emitter.unstructured(block));
        }
    }
    if record_patterns.is_some_and(|plans| !plans.all_claimed()) {
        return Err(StructureError::ExceptionHandlers);
    }
    emitter.lines.retain(|line| !line.detached_declaration);
    Ok(emitter.lines)
}

struct Emitter<'a> {
    instructions: &'a [Instruction],
    graph: &'a ControlFlowGraph,
    layout: Layout,
    exceptions: &'a Exceptions,
    exception_redirects: BTreeMap<usize, ExceptionRedirect>,
    resource_epilogue: Option<(usize, u32)>,
    assertions: Option<&'a assertions::Sites>,
    record_patterns: Option<&'a pattern_record::Plans>,
    cycle_rollout: Option<irreducible::Cycle>,
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
        self.run_region(block, region, machine, depth, pending, false, None)
    }

    fn run_region<'a, 'c>(
        &mut self,
        mut block: usize,
        region: Region<'_, 'a, 'c>,
        machine: &mut Machine<'a, 'c>,
        depth: usize,
        pending: &mut Vec<u32>,
        mut enter_loop: bool,
        mut first_instruction: Option<usize>,
    ) -> Result<bool, StructureError> {
        // Bytecode need not originate from Java, so recursion depth is not
        // constrained by the nesting limits of a source compiler.
        if depth > 128 {
            return Err(StructureError::Nesting);
        }
        loop {
            if let Some(scope) = region.predicate
                && let Some(outcome) = scope.outcome(block)
            {
                self.predicate_exit(scope, outcome, machine, depth, pending)?;
                return Ok(false);
            }
            if self.record_finally_label_break(block, region, machine, depth, pending)? {
                return Ok(false);
            }
            block = self.exceptions.bypass_cleanup(block);
            let Some(next) = self.redirected_exception_block(block, region, machine, depth, pending)?
            else {
                return Ok(false);
            };
            block = next;
            let first_header = mem::take(&mut enter_loop);
            if !first_header {
                if self.record_conditional_case_exit(block, region, machine, depth, pending)? {
                    return Ok(false);
                }
                if region.stop == Some(block) {
                    return Ok(true);
                }
                if let Some(scope) = region.switch_exit()
                    && block == scope.target
                {
                    self.require_empty_stack(machine, block)?;
                    self.lines.push(scope.record(machine, depth, mem::take(pending)));
                    return Ok(false);
                }
                if let Some((scope, transfer)) = region.loop_transfer(block) {
                    self.emit_loop_transfer(
                        block, region, scope, transfer, machine, depth, pending,
                    )?;
                    return Ok(false);
                }
            }
            if let Some(next) = self.try_cycle_rollout(block, region, machine, depth, pending, first_instruction)? {
                block = next;
                continue;
            }
            if (!first_header && !self.layout.inside(block, region))
                || !self.exceptions.contains(region.exception_arm, block)
                || self.emitted[block]
            {
                return Err(self.unstructured(block));
            }
            let exception_body = self.layout.loops[block].and_then(|shape| shape.exception_body);
            if let Some(id) = self.exceptions.at_start(region.exception_arm, block)
                && (if first_header {
                    exception_body.is_some_and(|body| {
                        body == self.exceptions.region(id).body || Some(body) == region.exception_arm
                    })
                } else {
                    exception_body != Some(self.exceptions.region(id).body)
                })
            {
                let Some(next) = self.emit_exception(id, region, machine, depth, pending)? else {
                    return Ok(false);
                };
                block = next;
                continue;
            }
            if !first_header && let Some(loop_shape) = self.layout.loops[block] {
                if let Some(next) = self.emit_loop_with_finally_label(block, loop_shape, region, machine, depth)? {
                    block = next;
                    pending.clear();
                    continue;
                }
                let Some((exit, resume)) =
                    self.emit_loop(block, loop_shape, region, machine, depth, pending)?
                else {
                    return Ok(false);
                };
                first_instruction = resume;
                block = exit;
                continue;
            }
            let start = first_instruction
                .take()
                .or_else(|| region.for_loop_prefix(self.graph.blocks[block].instructions.start));
            if start.is_none() {
                if let Some(next) =
                    self.try_emit_pattern_switch(block, region, machine, depth, pending, &mut first_instruction)?
                {
                    let Some(next) = next else { return Ok(false) };
                    block = next;
                    continue;
                }
                if let Some(next) =
                    self.try_emit_string_switch(block, region, machine, depth, pending)?
                {
                    let Some(next) = next else { return Ok(false) };
                    block = next;
                    continue;
                }
            }
            self.emitted[block] = true;
            let first_line = self.lines.len();
            let (tail, binding) = if let Some(start) = start {
                (
                    self.lift_if_arm_start(
                        block,
                        start,
                        machine,
                        region,
                        depth,
                        mem::take(pending),
                    )?,
                    None,
                )
            } else {
                self.lift_instanceof_head(block, machine, region, depth, mem::take(pending))?
            };
            let Tail {
                effect,
                mut offsets,
                control,
            } = tail;
            match effect {
                Effect::None => {
                    let next = self.single_successor(block)?;
                    if self.record_labeled_break(block, next, region, machine, depth, first_line, &mut offsets)? {
                        return Ok(false);
                    }
                    block = next;
                    *pending = offsets;
                }
                Effect::Jump(target) => {
                    let next = self.single_successor(block)?;
                    if self.graph.block_at(target) != Some(next) {
                        return Err(self.unstructured(block));
                    }
                    if self.record_labeled_break(block, next, region, machine, depth, first_line, &mut offsets)? {
                        return Ok(false);
                    }
                    self.map_conditional_case_jump(block, next, region, &mut offsets);
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
                    let Some(next) = self.emit_if_or_labeled(
                        block,
                        region,
                        machine,
                        depth,
                        condition,
                        binding,
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
                    if let Some((target, start)) = self.try_default_constructor_switch(
                        block, region, machine, depth, &selector, &control,
                    ) {
                        block = target;
                        first_instruction = Some(start);
                        *pending = offsets;
                        continue;
                    }
                    let Some(next) = self.emit_switch_or_labeled(
                        block,
                        region,
                        machine,
                        depth,
                        selector,
                        &mut offsets,
                        control,
                    )?
                    else {
                        return Ok(false);
                    };
                    block = next;
                    *pending = offsets;
                }
                Effect::Return(value) => {
                    if value.is_none()
                        && let Some((epilogue, jump)) = self.resource_epilogue
                        && epilogue == block
                    {
                        self.resource_epilogue = None;
                        offsets.clear();
                        offsets.push(jump);
                    }
                    let text = value.map_or_else(
                        || Document::from("return;"),
                        |value| surrounded(value, "return ", ";"),
                    );
                    let mut line = Line::new(depth, text, offsets);
                    line.boolean_return = machine.last_boolean_return().map(|(fact, offset)| {
                        BooleanReturn::direct(fact, offset)
                    });
                    self.lines.push(line);
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
        machine.forget_assignment_aliases();
        while index < range.end {
            if self.exceptions.skips_instruction(index) || region.for_loop_omits(index) {
                machine.forget_assignment_aliases();
                index += 1;
                continue;
            }
            let instruction = &self.instructions[index];
            if instruction.opcode == 0x84
                && index + 2 < range.end
                && do_while::is_conditional(self.instructions[range.end - 1].opcode)
                && region.is_loop_test(block)
                && !self.exceptions.skips_instruction(index + 1)
                && !region.for_loop_omits(index + 1)
                && machine.step_loop_prefix_update(instruction, &self.instructions[index + 1])?
            {
                let load = &self.instructions[index + 1];
                offsets.extend(instruction.offset..load.offset + load.len);
                index += 2;
                continue;
            }
            if matches!(instruction.opcode, 0xbc | 0xbd)
                && let Some(consumed) = machine.try_array_initializer(
                    &self.instructions[index..range.end],
                    |relative, _| {
                        let index = index + relative;
                        !self.exceptions.skips_instruction(index) && !region.for_loop_omits(index)
                    },
                )
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
            let initialized_this = machine.this_is_initialized();
            let folded = if matches!(instruction.opcode, 0x59..=0x73 | 0x78..=0x83) {
                machine.step_assignment(&self.instructions[index..range.end], |relative, _| {
                    let index = index + relative;
                    !self.exceptions.skips_instruction(index) && !region.for_loop_omits(index)
                })?
            } else {
                None
            };
            let (end, effect, instruction) = if let Some(step) = folded {
                if let Some(declaration) = step.declaration {
                    self.push(depth, declaration, Vec::new());
                }
                let end = index + step.consumed;
                offsets.extend(self.instructions[index..end].iter()
                    .filter(|op| !matches!(op.opcode, 0x59..=0x5e))
                    .flat_map(|op| op.offset..op.offset + op.len));
                (end, step.effect, &self.instructions[end - 1])
            } else {
                if index + 1 == range.end {
                    control = machine.control_order(instruction)?;
                }
                (index + 1, machine.step(instruction)?, instruction)
            };
            if !initialized_this && machine.this_is_initialized()
                && (depth != 0
                    || (matches!(&effect, Effect::Statement(text) if text == "super();")
                        && !self.lines.is_empty() && machine.requires_implicit_record_super()?))
            {
                return Err(self.unstructured(block));
            }
            if let Some(baseline) = region.protected
                && matches!(instruction.opcode, 0x36..=0x4e)
                && !machine.keeps_locals_of(baseline)
            {
                return Err(StructureError::LocalJoin {
                    offset: instruction.offset,
                });
            }
            let prelude = machine.take_prelude();
            if end == index + 1 && machine.instruction_has_source()
                && (!prelude.is_empty() || !matches!(effect, Effect::Jump(_)))
            {
                offsets.extend(instruction.offset..instruction.offset + instruction.len);
            }
            for statement in prelude {
                self.push(depth, statement, mem::take(&mut offsets));
            }
            if instruction.len == 0 && matches!(effect, Effect::Return(None)) {
                // No explicit bytecode return exists. A pure value discarded
                // at the end cannot acquire a source location on the brace.
                offsets.clear();
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
                transfer if end == range.end => tail = transfer,
                _ => return Err(self.unstructured(block)),
            }
            index = end;
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
        mut binding: Option<instanceof_patterns::Binding>,
        offsets: &mut Vec<u32>,
        mut control: RangeInclusive<u32>,
    ) -> Result<Option<usize>, StructureError> {
        if self.assertion_starts(block) {
            return self.emit_assertion(block, region, machine, depth, offsets);
        }
        if binding.is_none() {
            binding = self.record_instanceof_binding(block, machine, &mut condition, offsets)?;
        }
        let condition_end = *control.end();
        let condition_facts = machine.last_boolean_condition();
        let held = machine.hold_control_stack(&control)?;
        let prelude = machine.take_prelude();
        let labeled_tail = region.label_scope().and_then(|scope| scope.head_tail(block));
        let mut assigned_test = None;
        if let Some(local) = &mut binding {
            if !self.collapse_instanceof_guard(
                block,
                region,
                machine,
                depth,
                &mut condition,
                local,
                offsets,
                &mut control,
            )? {
                binding = None;
            }
        } else if labeled_tail.is_none() && let Some(proof) = self.collapse_instanceof_prefix(
            block,
            region,
            machine,
            depth,
            &mut condition,
            offsets,
            &mut control,
        )? {
            binding = proof;
        } else if labeled_tail.is_none() {
            assigned_test = self.collapse_assigned_test(
                block,
                region,
                machine,
                &mut condition,
                offsets,
                &mut control,
            );
            if assigned_test.is_none() {
                self.collapse_condition(
                    block,
                    region,
                    machine,
                    depth,
                    &mut condition,
                    offsets,
                    &mut control,
                )?;
                self.collapse_decision_graph(block, region, machine, &mut condition, offsets, &mut control);
            }
        }
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
        let normal_join = self.layout.normal_join(block, region);
        let shared_join = || self.layout.common_join(self.graph, region, [(fallthrough, None), (taken, None)]);
        // An enclosing continue or switch break can hide the common tail of
        // the ordinary paths. Give that tail one owner inside the construct.
        let switch_exit = region.switch_exit().is_some_and(|scope| {
            normal_join == Some(scope.target) && machine.stack_is_empty()
        });
        let join = if switch_exit || (normal_join.is_some() && normal_join == region.post_test_latch()) {
            shared_join().or(normal_join)
        } else {
            normal_join.or_else(shared_join)
        }
            .or_else(|| {
                let abrupt = |arm| {
                    // A physical return or rethrow may have been trimmed
                    // from the lexical join of this region.
                    region.predicate.is_some_and(|scope| scope.outcome(arm).is_some())
                        || region.conditional_case_scope().is_some_and(|scope| scope.guard(arm, region))
                        || (region.stop != Some(arm)
                            && (region.loop_transfer(arm).is_some()
                                || self.is_terminal(arm)
                                    && (machine.this_is_initialized()
                                        || self.is_prologue_throw(arm, machine))))
                };
                let next = match (abrupt(taken), abrupt(fallthrough)) {
                    (true, false) => fallthrough,
                    (false, true) => taken,
                    _ => return None,
                };
                if binding.is_none()
                    && machine.simplify_boolean_returns()
                    && self.pair_boolean_terminal_paths(region, [fallthrough, taken])
                {
                    return None;
                }
                (region.stop == Some(next) || self.layout.inside(next, region)).then_some(next)
            })
            .or(region.stop);
        let join = labeled_tail.or(join);
        let guard_clause = binding
            .as_ref()
            .is_some_and(|binding| join.is_some_and(|next| binding.succeeds_at(next)));
        let join = self.instanceof_join(join, region, binding.as_ref());
        let arm_region = region.branch(join);
        let skip_fallthrough = self.skips_to_counted_latch(block, fallthrough, arm_region);
        let skip_taken = self.skips_to_counted_latch(block, taken, arm_region);
        let negate = if guard_clause {
            binding
                .as_ref()
                .is_some_and(|binding| binding.succeeds_at(fallthrough))
        } else {
            join == Some(fallthrough)
                || skip_fallthrough
                || self.instanceof_empty_arm(binding.as_ref(), join, fallthrough)
        };
        let (then_at, else_at, condition, inverse) = if negate {
            (taken, fallthrough, when_true, when_false)
        } else {
            (fallthrough, taken, when_false, when_true)
        };
        let skip_else = if negate { skip_fallthrough } else { skip_taken };
        let condition_facts = if condition_end == *control.end() && binding.is_none() {
            condition_facts.orient(negate)
        } else {
            BooleanCondition::UNKNOWN
        };
        let test = (&condition, &inverse, condition_facts);

        let start = self.lines.len();
        let arm_entry = |target| {
            assigned_test
                .as_ref()
                .filter(|test| test.target.is_none_or(|assigned| assigned == target))
                .map_or(&*machine, |test| &test.state)
        };
        let then = self.instanceof_branch_arm(
            then_at, arm_region, arm_entry(then_at), depth + 1, binding.as_ref(),
        )?;
        let else_depth = if guard_clause { depth } else { depth + 1 };
        let otherwise = self.instanceof_branch_arm(
            else_at, arm_region, arm_entry(else_at), else_depth, binding.as_ref(),
        )?;
        if guard_clause && then.exit.is_some() {
            return Err(self.unstructured(block));
        }
        if assigned_test.is_none()
            && start == otherwise.end
            && let (Some(yes), Some(no)) = (&then.exit, &otherwise.exit)
            && yes.same_locals(machine)
            && no.same_locals(machine)
            && let Some(merge) = machine.merge_conditional_stack(yes, no, test, &control, held)?
        {
            if !merge.restored {
                for statement in prelude {
                    self.push(depth, statement, mem::take(offsets));
                }
            }
            if merge.uses_yes {
                offsets.extend(then.offsets);
            }
            if merge.uses_no {
                offsets.extend(otherwise.offsets);
            }
            return Ok(join);
        }
        if machine.has_uninitialized_stack() {
            return Err(self.unstructured(block));
        }
        if binding.is_none()
            && assigned_test.is_none()
            && let Some(mut line) = self.combine_boolean_returns([&then, &otherwise], depth, test)
        {
            for statement in prelude {
                self.push(depth, statement, mem::take(offsets));
            }
            let mut mapped = mem::take(offsets);
            mapped.append(&mut line.offsets);
            line.offsets = mapped;
            self.lines.push(line);
            return Ok(None);
        }

        let exits = [&then, &otherwise]
            .into_iter()
            .filter(|arm| arm.exit.is_some())
            .collect::<Vec<_>>();
        let (declarations, assignments) = if exits.is_empty() {
            (Vec::new(), Vec::new())
        } else {
            if let Some(test) = &assigned_test {
                machine.prefer_test_local(&test.state, test.slot);
            }
            self.merge_arms(machine, join.expect("reached an if join"), &exits)?
        };
        let mut assignments = assignments.into_iter();
        let mut assignment_lines = |line_depth: usize, falls: bool, mut offsets: Vec<u32>| {
            falls
                .then(|| assignments.next().expect("one assignment list per arm"))
                .unwrap_or_default()
                .into_iter()
                .map(|text| Line::new(line_depth, text, mem::take(&mut offsets)))
                .collect::<Vec<_>>()
        };
        let then_falls = then.exit.is_some();
        let else_falls = otherwise.exit.is_some();
        let then_end = then.end;
        let else_end = otherwise.end;
        let mut then_lines = assignment_lines(depth + 1, then_falls, then.offsets);
        let else_lines = assignment_lines(else_depth, else_falls, otherwise.offsets);
        if guard_clause {
            self.lines.splice(else_end..else_end, else_lines);
            then_lines.push(Line::new(depth, "}", Vec::new()));
        } else if (join != Some(else_at)
            && !skip_else
            && !self.instanceof_empty_arm(binding.as_ref(), join, else_at))
            || !else_lines.is_empty()
        {
            self.lines.splice(else_end..else_end, else_lines);
            then_lines.push(Line::new(depth, "} else {", Vec::new()));
        }
        self.lines.splice(then_end..then_end, then_lines);
        let mut header = Vec::new();
        for statement in prelude {
            header.push(Line::new(depth, statement, mem::take(offsets)));
        }
        if let Some(test) = assigned_test {
            header.push(Line::new(depth, test.declaration, Vec::new()));
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
        if !guard_clause {
            self.syntax(depth, "}");
        }
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
        allow_inverted: bool,
    ) -> Result<(usize, usize, Document, Option<instanceof_patterns::Binding>), StructureError>
    {
        let header = scope.header;
        self.emitted[header] = true;
        let (tail, mut binding) = if allow_inverted
            && let Some((tail, binding)) =
                self.lift_inverted_instanceof_loop_head(header, test.exit, iteration, region, depth)
        {
            (tail, Some(binding))
        } else {
            self.lift_instanceof_head(header, iteration, region, depth, Vec::new())?
        };
        let Tail {
            effect,
            mut offsets,
            control,
        } = tail;
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
        if let Some(local) = &mut binding {
            if !local.succeeds_at(test.exit)
                && !self.collapse_instanceof_guard(
                    header,
                    region,
                    iteration,
                    depth,
                    &mut condition,
                    local,
                    &mut offsets,
                    &mut control,
                )?
            {
                binding = None;
            }
        } else {
            self.collapse_condition(
                header,
                region,
                iteration,
                depth,
                &mut condition,
                &mut offsets,
                &mut control,
            )?;
        }
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
        if binding
            .as_ref()
            .is_some_and(|binding| !binding.succeeds_at(body) && !binding.succeeds_at(test.exit))
        {
            return Err(self.unstructured(header));
        }
        Ok((body, guard, condition, binding))
    }

    fn emit_loop<'a, 'c>(
        &mut self,
        header: usize,
        shape: Loop,
        region: Region<'_, 'a, 'c>,
        machine: &mut Machine<'a, 'c>,
        depth: usize,
        pending: &mut Vec<u32>,
    ) -> Result<Option<(usize, Option<usize>)>, StructureError> {
        for statement in machine.bind_edge_stack(self.offset(header), None)? {
            self.push(depth, statement, mem::take(pending));
        }
        pending.clear();
        let head_line = self.lines.len();
        if shape.wrapped.is_some() {
            let test = shape.post_test.ok_or_else(|| self.unstructured(header))?;
            self.emit_post_test_loop(header, test, region, machine, depth)?;
            self.lines[head_line].sequence_boundary = true;
            return Ok(Some((test.exit(), None)));
        }
        if let Some(test) = shape.post_test
            && let Some(exit) = self.try_post_test_loop(header, test, region, machine, depth)
        {
            self.lines[head_line].sequence_boundary = true;
            return Ok(Some((exit, None)));
        }
        let scope = Self::loop_scope(header, shape.exit, region, machine);
        self.syntax(depth, "while (true) {");
        let mut iteration = machine.clone();
        let mut for_loop = None;
        let mut exit_binding = None;
        let body_region = region.loop_body(&scope);
        let (repeats, guard) = if let Some(test) = shape.test {
            let (body, guard, condition, binding) =
                self.emit_loop_test(
                    &scope, test, body_region, &mut iteration, depth + 1, self.layout.inside(test.exit, region),
                )?;
            let body_region = if guard == head_line + 1
                && body == test.body
                && binding.is_none()
                && let Some(plan) = self.prove_for_loop(
                    header,
                    test,
                    region,
                    &scope.entry,
                    &mut iteration,
                    head_line,
                    depth,
                ) {
                if let Some(latch) = plan.latch {
                    scope.continue_at.set(latch);
                    self.emitted[latch] = true;
                }
                scope.update.set(plan.update);
                scope
                    .element_prefix
                    .set(plan.element.as_ref().map(|range| (range.start, range.end)));
                for_loop = Some(plan);
                region.loop_body(&scope)
            } else {
                body_region
            };
            let first_instruction = match binding {
                Some(binding) if binding.succeeds_at(body) => binding.enter(&mut iteration),
                other => {
                    exit_binding = other;
                    None
                }
            };
            let repeats = self.run_region(
                body,
                body_region,
                &mut iteration,
                depth + 1,
                pending,
                false,
                first_instruction,
            )?;
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
                    None,
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
            self.lines[head_line].sequence_boundary = true;
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
        if exit_binding.is_some()
            && (breaks.len() != 1 || !assignments[0].is_empty()
                || guard.as_ref().is_none_or(|(line, _)| *line != head_line + 1))
        {
            return Err(self.unstructured(header));
        }
        let mut recovered_condition = None;
        if let Some((guard_line, condition)) = guard
            && guard_line == head_line + 1
            && assignments[0].is_empty()
        {
            let offsets = mem::take(&mut self.lines[guard_line].offsets);
            if for_loop.is_some() {
                self.lines[head_line].offsets = offsets;
                recovered_condition = Some(condition);
            } else {
                self.lines[head_line] =
                    Line::new(depth, surrounded(condition, "while (", ") {"), offsets);
            }
            self.lines.drain(guard_line..guard_line + 3);
        }
        if for_loop.is_none() {
            self.label_loop(head_line, &scope);
        }
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
        let mut head_line = head_line;
        if let Some(plan) = for_loop {
            let condition = recovered_condition.ok_or_else(|| self.unstructured(header))?;
            head_line -= plan.write(&mut self.lines, head_line, condition, machine);
            self.label_loop(head_line, &scope);
        }
        self.lines.splice(
            head_line..head_line,
            stack
                .declarations
                .into_iter()
                .chain(locals.declarations)
                .map(|text| Line::new(depth, text, Vec::new())),
        );
        self.lines[head_line].sequence_boundary = true;
        Ok(Some((exit, exit_binding.and_then(|binding| binding.enter(machine)))))
    }

    fn loop_scope<'a, 'c>(
        header: usize,
        exit: Option<usize>,
        region: Region<'_, 'a, 'c>,
        machine: &Machine<'a, 'c>,
    ) -> LoopScope<'a, 'c> {
        LoopScope {
            header,
            continue_at: Cell::new(header),
            update: Cell::new(None),
            element_prefix: Cell::new(None),
            exit,
            entry: machine.clone(),
            breaks: RefCell::default(),
            test_continues: None,
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
        if region.exception_arm != scope.exception_arm
            && !(machine.stack_is_empty()
                && (self.exceptions.allows_finally_loop_transfer(
                    region.exception_arm,
                    scope.exception_arm,
                    target,
                ) || (transfer == Transfer::Break
                    && self.exceptions.allows_loop_break(
                        region.exception_arm,
                        scope.exception_arm,
                        scope.header,
                        target,
                    )))
                && machine.same_live_loop_bindings(&scope.entry, |slot| {
                    self.local_is_live(target, slot)
                }))
        {
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
                if let Some(continues) = &scope.test_continues {
                    if !machine.stack_is_empty()
                        || !machine.same_live_loop_bindings(&scope.entry, |slot| self.local_is_live(target, slot))
                    {
                        return Err(self.unstructured(target));
                    }
                    continues.set(true);
                } else {
                    self.emit_backedge(scope, machine, depth, offsets)?;
                }
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
        let instructions = self.instructions;
        let instruction = &instructions[self.graph.blocks[block].instructions.end - 1];
        let (default_offset, cases) = match dispatch {
            Some(dispatch) => (dispatch.default, dispatch.cases.as_slice()),
            None => match &instruction.operand {
                Operand::Switch { default, cases } => (*default, cases.as_slice()),
                _ => return Err(self.unstructured(block)),
            },
        };
        let default = self
            .graph
            .block_at(default_offset)
            .ok_or_else(|| self.unstructured(block))?;
        let mut groups = BTreeMap::<usize, Vec<CaseLabel>>::new();
        groups.entry(default).or_default();
        let mut numeric = dispatch.is_none();
        for &(key, target) in cases {
            let target = self
                .graph
                .block_at(target)
                .ok_or_else(|| self.unstructured(block))?;
            // Restore dense table aliases only after expression recovery has declined.
            if target != default || dispatch.is_some() {
                let (text, offsets) = if let Some(dispatch) = dispatch {
                    let (text, offsets) = dispatch.label(key);
                    (Document::from(text), offsets)
                } else {
                    let label = machine.enum_switch_label(instruction.offset, key);
                    numeric &= label.is_none();
                    let text = label.unwrap_or_else(|| key.to_string().into());
                    (text, Vec::new())
                };
                groups
                    .entry(target)
                    .or_default()
                    .push(CaseLabel { text, offsets });
            }
        }
        let labeled_tail = region.label_scope().and_then(|scope| scope.head_tail(block));
        let projected = region.conditional_case_scope().map(|scope| scope.plan())
            .filter(|plan| plan.head == block);
        // A default-only enum dispatch has no non-default label with which to
        // distinguish its selector from an integer selector.
        let numeric = numeric && groups.len() > 1 && labeled_tail.is_none();
        if projected.is_none() && labeled_tail.is_none() && let Some((condition, schedule)) = self.try_predicate_switch(
            block, region, machine, depth, &selector, &groups, default, &control,
        ) {
            return self.emit_if(block, region, machine, depth, condition, None, offsets, schedule);
        }
        if projected.is_none() && labeled_tail.is_none() && dispatch.is_none()
            && let Some(next) = self.try_complex_predicate_switch(
                block, region, machine, depth, &selector, &groups, default, offsets, &control,
            )?
        {
            return Ok(next);
        }
        let shared_join = || {
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
        };
        let join = projected.map(|plan| plan.switch_join()).or(labeled_tail).or_else(|| {
            let normal = self.layout.normal_join(block, region);
            // A continue can jump past the remainder of the loop body.
            // Keep that remainder outside the switch when its cases share it.
            if normal.is_some_and(|next| {
                matches!(region.loop_transfer(next), Some((_, Transfer::Continue)))
            }) {
                shared_join().or(normal)
            } else {
                normal.or_else(shared_join)
            }
        }).or(region.stop);
        if projected.is_none() && labeled_tail.is_none() && let Some(join) = join
            && self.try_switch_expression(
                block, region, machine, depth, &selector, &groups, default, join, &control,
            )
        {
            return Ok(Some(join));
        }
        if machine.has_uninitialized_stack() {
            return Err(self.unstructured(block));
        }
        let scope = join.filter(|_| labeled_tail.is_none()).map(|target| switch_exit::Scope::new(target, region));
        let mut switch_region = region.switch_body(join);
        switch_region.switch_scope = scope.as_ref();
        let falls_through = |layout: &Layout, target, next| {
            projected.map_or_else(
                || layout.can_fall_through(target, next, join),
                |plan| plan.falls_through(target, next),
            )
        };
        let has_fallthrough = || {
            let targets = groups.keys().copied();
            targets
                .clone()
                .zip(targets.skip(1))
                .any(|(target, next)| falls_through(&self.layout, target, next))
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
        let scoped_arms = machine.switch_requires_case_scopes();
        let mut ordered = (numeric || dispatch.is_some())
            .then(|| {
                numeric_switch::order(
                    mem::take(&mut groups),
                    cases,
                    default_offset,
                    match (dispatch.is_some(), instruction.opcode) {
                        (true, _) => numeric_switch::Keys::Projected,
                        (false, 0xaa) => numeric_switch::Keys::DenseIntegers,
                        _ => numeric_switch::Keys::SparseIntegers,
                    },
                    |target| self.offset(target),
                    |target, next| falls_through(&self.layout, target, next),
                )
            })
            .unwrap_or_default()
            .into_iter();
        let mut closing_return = None;
        let mut implicit_break = None;
        let mut empty_default = None;
        let mut groups = groups.into_iter().peekable();
        while let Some((target, keys, fallthrough)) = ordered
            .next()
            .map(|arm| (arm.target, arm.labels, arm.fallthrough))
            .or_else(|| {
                let (target, keys) = groups.next()?;
                let fallthrough = groups
                    .peek()
                    .map(|&(next, _)| next)
                    .filter(|&next| falls_through(&self.layout, target, next));
                Some((target, keys, fallthrough))
            })
        {
            let last = ordered.len() == 0 && groups.peek().is_none();
            let prior_implicit_break = implicit_break.take();
            let default_line = (last && (!numeric || projected.is_some_and(|plan| plan.omit_default()))
                && !scoped_arms && labeled_tail.is_none()
                && target == default && join == Some(default) && keys.is_empty()
                && !arms.is_empty())
                .then_some(self.lines.len());
            let arm_region = if let Some(next) = fallthrough {
                switch_region.branch(Some(next))
            } else {
                switch_region
            };
            let mut keys = keys.into_iter().peekable();
            while let Some(CaseLabel { mut text, offsets }) = keys.next() {
                text.insert_str(0, "case ");
                text.push_str(if scoped_arms && keys.peek().is_none() && target != default {
                    ": {"
                } else {
                    ":"
                });
                self.push(depth + 1, text, offsets);
            }
            if target == default {
                self.syntax(depth + 1, if scoped_arms { "default: {" } else { "default:" });
            }
            let arm = self.branch_arm(target, arm_region, machine, depth + 2)?;
            if dispatch.is_some() && last && join.is_none() && target == default && arm.exit.is_none()
                && let Some((jump, ret)) = string_switch::exclusive_return_edge(self.graph, instructions, target)
                && let Some(line) = self.lines.get_mut(arm.start..arm.end).and_then(|lines| lines.last_mut())
                && line.text.starts_with("return ") && line.offsets.contains(&ret.start)
            {
                // The exclusive post-switch return is now inside this arm.
                // Its value retains its origin; the source break owns the
                // old jump site on that same return line.
                line.offsets.push(jump);
                line.text.omit_bytes(ret);
            }
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
                    if let Some(line) = default_line
                        && arm.start == arm.end && arm.offsets.is_empty()
                    {
                        empty_default = Some((line, prior_implicit_break));
                    }
                    arms.push(arm);
                    if labeled_tail.is_none() || !last {
                        let direct_exit = join
                            .filter(|&join| self.graph.blocks[target].successors.as_slice() == [join])
                            .map(|_| &instructions[self.graph.blocks[target].instructions.end - 1]);
                        let jump = direct_exit.filter(|op| matches!(op.opcode, 0xa7 | 0xc8));
                        if !last || direct_exit.is_none() || jump.is_some() {
                            if direct_exit.is_some() && jump.is_none() {
                                implicit_break = Some(self.lines.len());
                            }
                            // A structural break owns the jump site, not the
                            // encoded destination bytes of the JVM branch.
                            let mapped = jump.map_or_else(Vec::new, |op| vec![op.offset]);
                            self.push(depth + 2, "break;", mapped);
                        }
                    }
                }
            } else if numeric
                && last
                && depth == 0
                && region.stop.is_none()
                && join.is_none()
                && arm.start < arm.end
                && self.lines.last().is_some_and(|line| {
                    line.depth == depth + 2 && line.text == "return;"
                })
            {
                // The last arm can reach the enclosing method's implicit
                // void return. Retain its mapping for the method's closing brace.
                closing_return = self.lines.pop();
            }
            if scoped_arms {
                self.syntax(depth + 1, "}");
            }
        }
        self.syntax(depth, "}");
        if let Some(mut line) = closing_return {
            line.depth = depth;
            self.lines.push(line);
        }
        let normal_count = arms.len();
        if let Some(scope) = scope {
            let target_offset = self.offset(scope.target);
            scope.append_arms(&mut self.lines, start, target_offset, &mut arms)?;
        }
        if arms.is_empty() {
            return Ok(None);
        }
        let join = join.expect("reached a switch join");
        let exits = arms.iter().collect::<Vec<_>>();
        let (declarations, assignments) = self.merge_arms(machine, join, &exits)?;
        if let Some((line, trailing_break)) = empty_default
            && normal_count.checked_sub(1).and_then(|index| assignments.get(index)).is_some_and(Vec::is_empty)
        {
            // The unmatched selector is a real incoming edge even when it
            // needs no source label. Omit it only after edge-copy analysis.
            self.lines.drain(line..self.lines.len() - 1);
            if let Some(line) = trailing_break {
                self.lines.remove(line);
            }
        }
        switch_exit::write_join_copies(&mut self.lines, arms, assignments, normal_count, depth + 2);
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
        let locals = machine.merge_locals_with_hoists(
            &exits,
            offset,
            |slot| self.layout.local_is_live(self.graph, self.instructions, join, slot),
            |arm, declaration, name, retarget| {
                local_joins::prove_local_relocation(&self.lines, arms[arm], declaration, name, retarget)
            },
        )?;
        for hoist in locals.hoists {
            for &(index, prefix) in &hoist.sites {
                let line = &mut self.lines[index];
                if let Some(prefix) = prefix {
                    hoist.rewrite(&mut line.text, prefix);
                } else {
                    // Retain arm indices until statement rendering; the
                    // uninitialized declaration has no evaluation or offsets.
                    line.detached_declaration = true;
                }
            }
        }
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
        let at_loop_entry = region.loop_header == Some(start)
            && self.layout.loops[start].and_then(|shape| shape.exception_body) == region.exception_arm
            && region.exception_arm.is_some();
        if region.stop == Some(start) && !at_loop_entry {
            return Ok(true);
        }
        let mut arm = baseline.clone();
        let reaches = if let Some(shape) = self.layout.loops[start]
            .filter(|_| at_loop_entry)
            .and_then(Loop::wrapped_while)
        {
            let expected = shape.exit.expect("wrapped while has an exit");
            let exit = self.emit_loop(start, shape, region, &mut arm, depth, &mut Vec::new())?;
            if exit != Some((expected, None)) || region.stop != Some(expected) {
                return Err(self.unstructured(start));
            }
            true
        } else {
            self.run_region(start, region, &mut arm, depth, &mut Vec::new(), at_loop_entry, None)?
        };
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

    fn is_prologue_throw(&self, block: usize, machine: &Machine<'_, '_>) -> bool {
        let Some((last, body)) = self.instructions[self.graph.blocks[block].instructions.clone()]
            .split_last()
        else {
            return false;
        };
        // Both sides of a fail-fast check may be terminal in the JVM graph:
        // the other arm can initialize this and then return or throw. Keep
        // that arm at the enclosing depth so its constructor call is legal.
        last.opcode == 0xbf && !body.iter().any(|op| machine.may_chain_constructor(op))
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

fn logical(left: Document, op: &str, right: Document) -> Document {
    let infix = match op {
        "&&" => Infix::AND,
        "||" => Infix::OR,
        _ => unreachable!("non-short-circuit operator"),
    };
    Document::infix_expression(
        infix,
        [&left, &right].map(|operand| {
            (operand, operand.infix().is_some_and(|child| child.precedence < infix.precedence))
        }),
    )
}
