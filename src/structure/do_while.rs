// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use std::cell::Cell;

use crate::{
    bytecode::Instruction,
    cfg::{ControlFlowGraph, NaturalLoop},
    lift::{Effect, Machine},
};

use super::{Condition, Emitter, Region, StructureError, Tail, surrounded};

#[cfg(test)]
mod tests;

pub(super) fn is_conditional(opcode: u8) -> bool {
    matches!(opcode, 0x99..=0xa6 | 0xc6..=0xc7)
}

#[derive(Clone, Copy)]
pub(super) struct PostTest {
    start: usize,
    latch: usize,
    exit: usize,
}

impl PostTest {
    pub(super) fn classify(
        graph: &ControlFlowGraph,
        instructions: &[Instruction],
        natural: &NaturalLoop,
    ) -> Option<Self> {
        let &[latch] = natural.latches.as_slice() else { return None };
        let header = natural.header;
        let exit = match graph.blocks[latch].successors.as_slice() {
            &[first, second] if first == header => second,
            &[first, second] if second == header => first,
            _ => return None,
        };
        let test = |block: usize, back: usize| {
            let node = &graph.blocks[block];
            node.successors.len() == 2
                && node.successors.contains(&back)
                && node.successors.contains(&exit)
                && node.exception_predecessors.is_empty()
                && node.exception_successors.is_empty()
                && is_conditional(instructions[node.instructions.end - 1].opcode)
        };
        if !test(latch, header) {
            return None;
        }
        let mut start = latch;
        while start != header {
            let &[pred] = graph.blocks[start].predecessors.as_slice() else { break };
            if pred == header || natural.blocks.binary_search(&pred).is_err() || !test(pred, start) {
                break;
            }
            start = pred;
        }
        Some(Self { start, latch, exit })
    }

    pub(super) fn exit(self) -> usize {
        self.exit
    }
}

impl Emitter<'_> {
    pub(super) fn try_post_test_loop<'a, 'c>(
        &mut self,
        header: usize,
        test: PostTest,
        region: Region<'_, 'a, 'c>,
        entry: &Machine<'a, 'c>,
        depth: usize,
    ) -> Option<usize> {
        if region.exception_arm.is_some()
            || !entry.stack_is_empty()
            || !self.post_test_region(header, test, region)
        {
            return None;
        }
        // A structurally valid latch may still require statements or local
        // copies that Java cannot express in a do-while test. Don't change
        // the ordinary loop when this more specific source form fails.
        let line = self.lines.len();
        let emitted = self.emitted.clone();
        let names = entry.local_name_checkpoint();
        if self.emit_post_test_loop(header, test, region, entry, depth).is_ok() {
            return Some(test.exit);
        }
        self.lines.truncate(line);
        self.emitted = emitted;
        entry.restore_local_names(names);
        None
    }

    fn post_test_region(&self, header: usize, test: PostTest, region: Region<'_, '_, '_>) -> bool {
        if test.start != header
            && (!self.layout.direct_loop_member(test.start, header)
                || self.layout.loops[test.start].is_some()
                || !self.layout.direct_loop_member(test.latch, header))
        {
            return false;
        }
        let mut seen = vec![false; self.graph.blocks.len()];
        let mut pending = vec![header];
        while let Some(block) = pending.pop() {
            if block == test.exit || std::mem::replace(&mut seen[block], true) {
                continue;
            }
            // The tentative emitter must not mark an enclosing loop or
            // mutate exception regions. Keep those loop/handler edges in
            // the ordinary structurer rather than speculating across them.
            let node = &self.graph.blocks[block];
            if region.loop_transfer(block).is_some() || region.stop == Some(block)
                || !node.exception_successors.is_empty() || !node.exception_predecessors.is_empty()
                || self.exceptions.at_start(None, block).is_some()
                || self.exceptions.bypass_cleanup(block) != block
                || self.exception_redirects.contains_key(&block)
            {
                return false;
            }
            pending.extend_from_slice(&node.successors);
        }
        true
    }

    pub(super) fn emit_post_test_loop<'a, 'c>(
        &mut self,
        header: usize,
        test: PostTest,
        region: Region<'_, 'a, 'c>,
        entry: &Machine<'a, 'c>,
        depth: usize,
    ) -> Result<(), StructureError> {
        let mut scope = Self::loop_scope(header, Some(test.exit), region, entry);
        scope.continue_at.set(test.start);
        if test.start != header {
            scope.test_continues = Some(Cell::default());
        }
        let body = region.loop_body(&scope);
        let head_line = self.lines.len();
        self.syntax(depth, "do {");
        let mut iteration = entry.clone();
        let mut pending = Vec::new();
        let tail = if test.start == header {
            self.emitted[header] = true;
            self.lift_inline_post_test(header, body, entry, &mut iteration, depth + 1)?
        } else {
            let reaches = self.run_region(header, body, &mut iteration, depth + 1, &mut pending, true, None)?;
            if !reaches {
                if !scope.test_continues.as_ref().is_some_and(Cell::get) {
                    return Err(self.unstructured(test.start));
                }
                iteration = entry.clone();
            }
            if self.emitted[test.start]
                || !iteration.stack_is_empty()
                || !iteration.same_live_loop_bindings(entry, |slot| self.local_is_live(test.start, slot))
            {
                return Err(self.unstructured(test.start));
            }
            self.emitted[test.start] = true;
            let start = self.lines.len();
            let tail = self.lift_block(test.start, &mut iteration, body, depth + 1, pending)?;
            if self.lines.len() != start {
                return Err(self.unstructured(test.start));
            }
            tail
        };
        let Tail {
            effect: Effect::Branch { target, when_true, when_false },
            mut offsets,
            control: Some(mut control),
        } = tail else { return Err(self.unstructured(test.start)) };
        if !iteration.stack_is_empty() {
            return Err(self.unstructured(test.start));
        }
        iteration.freeze_control_stack(&control)?;
        if !iteration.take_prelude().is_empty() {
            return Err(self.unstructured(test.start));
        }
        let (taken, fallthrough) = self.branch_targets(test.start, target)?;
        let mut condition = Condition { taken, fallthrough, when_true, when_false };
        self.collapse_condition(test.start, body, &mut iteration, depth + 1, &mut condition, &mut offsets, &mut control)?;
        let condition = match (condition.taken, condition.fallthrough) {
            (back, exit) if back == header && exit == test.exit => condition.when_true,
            (exit, back) if back == header && exit == test.exit => condition.when_false,
            _ => return Err(self.unstructured(test.start)),
        };
        if !self.emitted[test.latch]
            || !iteration.same_live_loop_bindings(entry, |slot| self.local_is_live(header, slot) || self.local_is_live(test.exit, slot))
            || scope.breaks.borrow().iter().any(|edge| {
                !edge.stack_is_empty() || !edge.same_live_loop_bindings(entry, |slot| self.local_is_live(test.exit, slot))
            })
        {
            return Err(self.unstructured(test.start));
        }
        for line in &mut self.lines[head_line + 1..] {
            if line.loop_break.as_ref().is_some_and(|edge| edge.header == header) {
                line.loop_break = None;
            }
        }
        self.label_loop(head_line, &scope);
        self.push(depth, surrounded(condition, "} while (", ");"), offsets);
        Ok(())
    }

    fn lift_inline_post_test<'a, 'c>(
        &mut self,
        header: usize,
        region: Region<'_, 'a, 'c>,
        entry: &Machine<'a, 'c>,
        iteration: &mut Machine<'a, 'c>,
        depth: usize,
    ) -> Result<Tail, StructureError> {
        let body = self.lines.len();
        let tail = self.lift_block(header, iteration, region, depth, Vec::new())?;
        if self.lines.len() == body {
            return Err(self.unstructured(header));
        }
        let block = self.graph.blocks[header].instructions.clone();
        let start = block.start + self.instructions[block.clone()]
            .binary_search_by_key(tail.offsets.first().ok_or_else(|| self.unstructured(header))?, |op| op.offset)
            .map_err(|_| self.unstructured(header))?;
        if start == block.start || !iteration.same_live_loop_bindings(entry, |slot| {
            self.instructions[start..block.end].iter().any(|op| super::for_loops::local_slot(op) == Some(slot))
        }) {
            return Err(self.unstructured(header));
        }
        // Prove the inline suffix is a self-contained expression. In
        // particular, it may not refer to a synthetic temporary declared in
        // a statement of the do body, whose Java scope ends before the test.
        let mut probe = entry.clone();
        let after_body = self.lines.len();
        let check = self.lift_range(header, start..block.end, &mut probe, region, depth, Vec::new())?;
        if self.lines.len() != after_body || !same_branch(&tail.effect, &check.effect) {
            return Err(self.unstructured(header));
        }
        Ok(tail)
    }
}

fn same_branch(a: &Effect, b: &Effect) -> bool {
    matches!((a, b), (
        Effect::Branch { target: at, when_true: ay, when_false: an },
        Effect::Branch { target: bt, when_true: by, when_false: bn },
    ) if at == bt && ay == by && an == bn)
}
