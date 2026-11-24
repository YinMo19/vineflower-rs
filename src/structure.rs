// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

mod flow;
mod protected;
#[cfg(test)]
mod tests;

use std::collections::BTreeMap;
use std::mem;

use thiserror::Error;

use crate::bytecode::{Instruction, Operand};
use crate::cfg::ControlFlowGraph;
use crate::classfile::ExceptionHandler;
use crate::lift::{Effect, LiftError, Machine};

use self::flow::{Layout, Region, While};
use self::protected::Try;

#[derive(Debug)]
pub(crate) struct Line {
    pub depth: usize,
    pub text: String,
    pub offsets: Vec<u32>,
}

#[derive(Debug, Error)]
pub(crate) enum StructureError {
    #[error(transparent)]
    Lift(#[from] LiftError),
    #[error("unsupported exception handling region")]
    ExceptionHandlers,
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

pub(crate) fn structure(
    instructions: &[Instruction],
    graph: &ControlFlowGraph,
    machine: Machine<'_, '_>,
) -> Result<Vec<Line>, StructureError> {
    if graph
        .blocks
        .iter()
        .any(|block| !block.exception_successors.is_empty())
    {
        return Err(StructureError::ExceptionHandlers);
    }
    structure_regions(instructions, graph, machine, None)
}

pub(crate) fn structure_with_handlers(
    instructions: &[Instruction],
    graph: &ControlFlowGraph,
    machine: Machine<'_, '_>,
    handlers: &[ExceptionHandler],
) -> Result<Vec<Line>, StructureError> {
    if handlers.is_empty() {
        return structure(instructions, graph, machine);
    }
    let try_shape = Try::new(instructions, graph, handlers)?;
    structure_regions(instructions, graph, machine, Some(try_shape))
}

fn structure_regions(
    instructions: &[Instruction],
    graph: &ControlFlowGraph,
    mut machine: Machine<'_, '_>,
    try_shape: Option<Try>,
) -> Result<Vec<Line>, StructureError> {
    if graph.blocks.is_empty() {
        return Ok(Vec::new());
    }
    let mut emitter = Emitter {
        instructions,
        graph,
        layout: Layout::new(graph, instructions)?,
        try_shape,
        emitted: vec![false; graph.blocks.len()],
        lines: Vec::new(),
    };
    emitter.region(0, Region::METHOD, &mut machine, 0)?;
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
    try_shape: Option<Try>,
    emitted: Vec<bool>,
    lines: Vec<Line>,
}

struct Tail {
    effect: Effect,
    offsets: Vec<u32>,
}

struct Condition {
    taken: usize,
    fallthrough: usize,
    when_true: String,
    when_false: String,
}

impl Emitter<'_> {
    /// Emits a region once. True means a path completes normally at its stop;
    /// false means all its paths return or throw.
    fn region<'a, 'c>(
        &mut self,
        mut block: usize,
        region: Region<'_, 'a, 'c>,
        machine: &mut Machine<'a, 'c>,
        depth: usize,
    ) -> Result<bool, StructureError> {
        // Bytecode need not originate from Java, so recursion depth is not
        // constrained by the nesting limits of a source compiler.
        if depth > 128 {
            return Err(StructureError::Nesting);
        }
        loop {
            if region.stop == Some(block) {
                return Ok(true);
            }
            if !self.layout.inside(block, region) || self.emitted[block] {
                return Err(self.unstructured(block));
            }
            if let Some(try_shape) = self.try_shape {
                if region.protected.is_some() {
                    if !try_shape.contains(block) {
                        return Err(self.unstructured(block));
                    }
                } else if block == try_shape.start {
                    let Some(next) = self.emit_try(try_shape, region, machine, depth)? else {
                        return Ok(false);
                    };
                    block = next;
                    continue;
                }
            }
            self.emitted[block] = true;
            if let Some(loop_shape) = self.layout.loops[block] {
                if !machine.this_is_initialized() {
                    return Err(self.unstructured(block));
                }
                self.emit_while(block, loop_shape, region, machine, depth)?;
                block = loop_shape.exit;
                continue;
            }
            let Tail { effect, offsets } =
                self.lift_block(block, machine, region.protected, depth)?;
            if !machine.this_is_initialized()
                && matches!(effect, Effect::Branch { .. } | Effect::Switch { .. })
            {
                return Err(self.unstructured(block));
            }
            match effect {
                Effect::None => block = self.single_successor(block)?,
                Effect::Jump(target) => {
                    let next = self.single_successor(block)?;
                    if self.graph.block_at(target) != Some(next) {
                        return Err(self.unstructured(block));
                    }
                    block = next;
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
                    let Some(next) =
                        self.emit_if(block, region, machine, depth, condition, offsets)?
                    else {
                        return Ok(false);
                    };
                    block = next;
                }
                Effect::Switch { selector } => {
                    let Some(next) =
                        self.emit_switch(block, region, machine, depth, selector, offsets)?
                    else {
                        return Ok(false);
                    };
                    block = next;
                }
                Effect::Return(value) => {
                    let text = value
                        .map_or_else(|| "return;".to_owned(), |value| format!("return {value};"));
                    self.push(depth, text, offsets);
                    return Ok(false);
                }
                Effect::Throw(value) => {
                    self.push(depth, format!("throw {value};"), offsets);
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
        protected: Option<&Machine<'a, 'c>>,
        depth: usize,
    ) -> Result<Tail, StructureError> {
        let mut range = self.graph.blocks[block].instructions.clone();
        if let Some(try_shape) = self.try_shape {
            if block == try_shape.handler {
                range.start += 1; // The catch clause declares the stored exception.
            } else if let Some(split) = try_shape.return_split
                && protected.is_some()
                && self.graph.blocks[split].instructions.start == range.end
            {
                if mem::replace(&mut self.emitted[split], true) {
                    return Err(self.unstructured(split));
                }
                range.end = self.graph.blocks[split].instructions.end;
            }
        }
        let mut offsets = Vec::new();
        let mut tail = Effect::None;
        for index in range.clone() {
            let instruction = &self.instructions[index];
            let effect = machine.step(instruction)?;
            if let Some(baseline) = protected
                && matches!(instruction.opcode, 0x36..=0x4e)
                && !machine.keeps_locals_of(baseline)
            {
                return Err(StructureError::LocalJoin {
                    offset: instruction.offset,
                });
            }
            let prelude = machine.take_prelude();
            // Nops and gotos eliminated by region formation have no source line.
            if !prelude.is_empty()
                || (instruction.opcode != 0 && !matches!(effect, Effect::Jump(_)))
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
                Effect::FieldAssignment { target, value } => {
                    self.push(
                        depth,
                        format!("{target} = {value};"),
                        mem::take(&mut offsets),
                    );
                }
                transfer if index + 1 == range.end => tail = transfer,
                _ => return Err(self.unstructured(block)),
            }
        }
        if !machine.stack_is_empty() {
            return Err(StructureError::StackJoin {
                offset: self.instructions[range.end - 1].offset,
            });
        }
        Ok(Tail {
            effect: tail,
            offsets,
        })
    }

    fn emit_if<'a, 'c>(
        &mut self,
        block: usize,
        region: Region<'_, 'a, 'c>,
        machine: &Machine<'a, 'c>,
        depth: usize,
        condition: Condition,
        offsets: Vec<u32>,
    ) -> Result<Option<usize>, StructureError> {
        let Condition {
            taken,
            fallthrough,
            when_true,
            when_false,
        } = condition;
        if taken == fallthrough {
            // Even a degenerate condition can evaluate a call or throw.
            self.push(depth, format!("if ({when_false}) {{"), offsets);
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
                let next = match (self.is_terminal(taken), self.is_terminal(fallthrough)) {
                    (true, false) => fallthrough,
                    (false, true) => taken,
                    _ => return None,
                };
                (region.stop == Some(next) || self.layout.inside(next, region)).then_some(next)
            })
            .or(region.stop);
        let arm_region = region.branch(join);
        let (then_at, else_at, condition) = if join == Some(fallthrough) {
            (taken, fallthrough, when_true)
        } else {
            (fallthrough, taken, when_false)
        };

        self.push(depth, format!("if ({condition}) {{"), offsets);
        let then_falls = self.scoped_arm(then_at, arm_region, machine, depth + 1)?;
        let else_falls = if join == Some(else_at) {
            true
        } else {
            self.syntax(depth, "} else {");
            self.scoped_arm(else_at, arm_region, machine, depth + 1)?
        };
        self.syntax(depth, "}");
        Ok(if then_falls || else_falls { join } else { None })
    }

    fn emit_while<'a, 'c>(
        &mut self,
        header: usize,
        loop_shape: While,
        region: Region<'_, 'a, 'c>,
        machine: &Machine<'a, 'c>,
        depth: usize,
    ) -> Result<(), StructureError> {
        let head_line = self.lines.len();
        self.syntax(depth, "while (true) {");
        let mut iteration = machine.clone();
        let Tail { effect, offsets } =
            self.lift_block(header, &mut iteration, region.protected, depth + 1)?;
        let Effect::Branch {
            target,
            when_true,
            when_false,
        } = effect
        else {
            return Err(self.unstructured(header));
        };
        let (taken, _) = self.branch_targets(header, target)?;
        let (condition, exit_condition) = if taken == loop_shape.body {
            (when_true, when_false)
        } else {
            (when_false, when_true)
        };
        if self.lines.len() == head_line + 1 {
            let line = &mut self.lines[head_line];
            line.text = format!("while ({condition}) {{");
            line.offsets = offsets;
        } else {
            // A header that emits statements must execute them on every test,
            // including the iteration on which the condition fails.
            self.push(depth + 1, format!("if ({exit_condition}) {{"), offsets);
            self.syntax(depth + 2, "break;");
            self.syntax(depth + 1, "}");
        }

        // Check the header's exit state separately from its backedge state.
        // Declarations made while computing the test are scoped to the loop.
        if !iteration.keeps_locals_of(machine) {
            return Err(StructureError::LocalJoin {
                offset: self.offset(loop_shape.exit),
            });
        }
        if self.region(
            loop_shape.body,
            region.loop_body(header),
            &mut iteration,
            depth + 1,
        )? {
            Self::check_scope(iteration, machine, self.offset(header))?;
        }
        self.syntax(depth, "}");
        Ok(())
    }

    fn emit_switch<'a, 'c>(
        &mut self,
        block: usize,
        region: Region<'_, 'a, 'c>,
        machine: &Machine<'a, 'c>,
        depth: usize,
        selector: String,
        offsets: Vec<u32>,
    ) -> Result<Option<usize>, StructureError> {
        let instruction = &self.instructions[self.graph.blocks[block].instructions.end - 1];
        let Operand::Switch { default, cases } = &instruction.operand else {
            return Err(self.unstructured(block));
        };
        let default = self
            .graph
            .block_at(*default)
            .ok_or_else(|| self.unstructured(block))?;
        let mut groups = BTreeMap::<usize, Vec<i32>>::new();
        groups.entry(default).or_default();
        for &(key, target) in cases {
            let target = self
                .graph
                .block_at(target)
                .ok_or_else(|| self.unstructured(block))?;
            // tableswitch pads missing keys with the default target.
            if target != default {
                groups.entry(target).or_default().push(key);
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
        let switch_region = region.branch(join);
        self.push(depth, format!("switch ({selector}) {{"), offsets);
        let mut joins = false;
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
            while let Some(key) = keys.next() {
                if keys.peek().is_none() {
                    self.push(depth + 1, format!("case {key}: {{"), Vec::new());
                } else {
                    self.push(depth + 1, format!("case {key}:"), Vec::new());
                }
            }
            if target == default {
                self.syntax(depth + 1, "default: {");
            }
            if self.scoped_arm(target, arm_region, machine, depth + 2)? && fallthrough.is_none() {
                self.syntax(depth + 2, "break;");
                joins = true;
            }
            self.syntax(depth + 1, "}");
        }
        self.syntax(depth, "}");
        Ok(if joins { join } else { None })
    }

    fn emit_try<'a, 'c>(
        &mut self,
        shape: Try,
        region: Region<'_, 'a, 'c>,
        machine: &Machine<'a, 'c>,
        depth: usize,
    ) -> Result<Option<usize>, StructureError> {
        if !machine.this_is_initialized() {
            return Err(self.unstructured(shape.start));
        }
        self.syntax(depth, "try {");
        let body_falls = self.scoped_arm(
            shape.start,
            region.try_body(shape.join, machine),
            machine,
            depth + 1,
        )?;
        let mut catch_machine = machine.clone();
        let store = &self.instructions[self.graph.blocks[shape.handler].instructions.start];
        let (ty, name) = catch_machine.bind_caught_exception(shape.catch_type, store)?;
        self.push(
            depth,
            format!("}} catch ({ty} {name}) {{"),
            (store.offset..store.offset + store.len).collect(),
        );
        let catch_falls = self.region(
            shape.handler,
            region.branch(shape.join),
            &mut catch_machine,
            depth + 1,
        )?;
        if catch_falls {
            Self::check_scope(
                catch_machine,
                machine,
                self.offset(shape.join.expect("reached the try join")),
            )?;
        }
        self.syntax(depth, "}");
        Ok(if body_falls || catch_falls {
            shape.join
        } else {
            None
        })
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

    fn push(&mut self, depth: usize, text: String, offsets: Vec<u32>) {
        self.lines.push(Line {
            depth,
            text,
            offsets,
        });
    }

    fn syntax(&mut self, depth: usize, text: &str) {
        self.push(depth, text.to_owned(), Vec::new());
    }
}
