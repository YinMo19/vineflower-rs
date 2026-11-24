// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::rc::Rc;

use crate::bytecode::{Instruction, Operand};
use crate::cfg::ControlFlowGraph;
use crate::lift::Machine;

use super::StructureError;
use super::assertions::Sites;
use super::do_while::PostTest;
use super::labeled_blocks::conditional_case::{ConditionalCase, ConditionalCaseScope};
use super::labeled_blocks::loop_exit::LoopExitLabel;
use super::protected::{ArmId, Exceptions};

#[derive(Clone, Copy)]
pub(super) struct Region<'r, 'a, 'c> {
    pub(super) stop: Option<usize>,
    pub(super) loop_header: Option<usize>,
    // A detached handler is lexically inside the loop even though normal
    // backedges do not put its CFG blocks in that loop.
    layout_loop_header: Option<usize>,
    pub(super) protected: Option<&'r Machine<'a, 'c>>,
    pub(super) exception_arm: Option<ArmId>,
    pub(super) switch_depth: usize,
    pub(super) switch_scope: Option<&'r super::switch_exit::Scope<'a, 'c>>,
    pub(super) predicate: Option<&'r super::switch_expression::predicate::Scope<'r, 'a, 'c>>,
    loop_scope: Option<&'r LoopScope<'a, 'c>>,
    label_scope: Option<&'r super::labeled_blocks::Scope<'a, 'c>>,
    conditional_case: Option<&'r ConditionalCaseScope<'r, 'a, 'c>>,
    outer: Option<&'r Region<'r, 'a, 'c>>,
}

impl<'r, 'a, 'c> Region<'r, 'a, 'c> {
    pub(super) const METHOD: Self = Self {
        stop: None,
        loop_header: None,
        layout_loop_header: None,
        protected: None,
        exception_arm: None,
        predicate: None,
        switch_depth: 0,
        switch_scope: None,
        loop_scope: None,
        label_scope: None,
        conditional_case: None,
        outer: None,
    };

    pub(super) fn branch(&'r self, stop: Option<usize>) -> Self {
        Self {
            stop,
            outer: Some(self),
            ..*self
        }
    }

    pub(super) fn predicate_body(&'r self, scope: &'r super::switch_expression::predicate::Scope<'r, 'a, 'c>) -> Self {
        Self { predicate: Some(scope), ..self.switch_body(None) }
    }

    pub(super) fn label_body(&'r self, scope: &'r super::labeled_blocks::Scope<'a, 'c>, stop: Option<usize>) -> Self {
        Self { label_scope: Some(scope), ..self.branch(stop) }
    }

    pub(super) fn label_scope(&self) -> Option<&'r super::labeled_blocks::Scope<'a, 'c>> {
        self.label_scope
    }

    pub(super) fn conditional_case_body(&'r self, scope: &'r ConditionalCaseScope<'r, 'a, 'c>) -> Self {
        Self { conditional_case: Some(scope), ..self.branch(self.stop) }
    }

    pub(super) fn conditional_case_scope(&self) -> Option<&'r ConditionalCaseScope<'r, 'a, 'c>> {
        self.conditional_case
    }

    pub(super) fn loop_body(&'r self, scope: &'r LoopScope<'a, 'c>) -> Self {
        Self {
            stop: Some(scope.continue_at.get()),
            loop_header: Some(scope.header),
            layout_loop_header: Some(scope.header),
            loop_scope: Some(scope),
            outer: Some(self),
            ..*self
        }
    }

    pub(super) fn switch_body(&'r self, stop: Option<usize>) -> Self {
        Self {
            switch_depth: self.switch_depth + 1,
            switch_scope: None,
            ..self.branch(stop)
        }
    }

    pub(super) fn switch_exit(self) -> Option<&'r super::switch_exit::Scope<'a, 'c>> {
        self.switch_scope.filter(|scope| scope.permits(self))
    }

    pub(super) fn loop_transfer(&self, block: usize) -> Option<(&'r LoopScope<'a, 'c>, Transfer)> {
        let mut current = Some(self);
        while let Some(region) = current {
            if let Some(scope) = region.loop_scope {
                if block == scope.continue_at.get() {
                    return Some((scope, Transfer::Continue));
                }
                if Some(block) == scope.exit {
                    return Some((scope, Transfer::Break));
                }
            }
            current = region.outer;
        }
        None
    }

    pub(super) fn for_loop_prefix(&self, start: usize) -> Option<usize> {
        let range = self.loop_scope?.element_prefix.get()?;
        (range.0 == start).then_some(range.1)
    }

    pub(super) fn for_loop_omits(&self, index: usize) -> bool {
        self.loop_scope
            .is_some_and(|scope| scope.update.get() == Some(index))
    }

    pub(super) fn counted_latch(&self) -> Option<usize> {
        let scope = self.loop_scope?;
        let latch = scope.continue_at.get();
        (latch != scope.header && scope.update.get().is_some()).then_some(latch)
    }

    pub(super) fn post_test_latch(&self) -> Option<usize> {
        let scope = self.loop_scope?;
        scope.test_continues.as_ref()?;
        Some(scope.continue_at.get())
    }

    pub(super) fn is_loop_test(&self, block: usize) -> bool {
        self.loop_header == Some(block) || self.post_test_latch() == Some(block)
    }

    pub(super) fn exception(
        &'r self,
        stop: Option<usize>,
        arm: ArmId,
        protected: Option<&'r Machine<'a, 'c>>,
    ) -> Self {
        Self {
            protected: protected.or(self.protected),
            exception_arm: Some(arm),
            ..self.branch(stop)
        }
    }

    pub(super) fn with_exception_layout(self, containing_loop: Option<usize>) -> Self {
        Self {
            layout_loop_header: containing_loop,
            ..self
        }
    }

    fn has_stop(&self, block: usize) -> bool {
        if self.predicate.is_some_and(|scope| !scope.cut.owns(block)) {
            return true;
        }
        let mut next = Some(self);
        while let Some(region) = next {
            if region.stop == Some(block) {
                return true;
            }
            next = region.outer;
        }
        false
    }
}

pub(super) struct LoopScope<'a, 'c> {
    pub(super) header: usize,
    pub(super) continue_at: Cell<usize>,
    pub(super) update: Cell<Option<usize>>,
    pub(super) element_prefix: Cell<Option<(usize, usize)>>,
    pub(super) exit: Option<usize>,
    pub(super) entry: Machine<'a, 'c>,
    pub(super) breaks: RefCell<Vec<Machine<'a, 'c>>>,
    pub(super) test_continues: Option<Cell<bool>>,
    pub(super) labeled: Cell<bool>,
    pub(super) switch_depth: usize,
    pub(super) exception_arm: Option<ArmId>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum Transfer {
    Break,
    Continue,
}

#[derive(Clone, Copy)]
pub(super) struct While {
    pub(super) body: usize,
    pub(super) exit: usize,
}

#[derive(Clone, Copy)]
pub(super) struct Loop {
    pub(super) test: Option<While>,
    pub(super) post_test: Option<PostTest>,
    pub(super) exit: Option<usize>,
    pub(super) exception_body: Option<ArmId>,
    pub(super) wrapped: Option<While>,
    parent: Option<usize>,
}

impl Loop {
    pub(super) fn wrapped_while(self) -> Option<Self> {
        let test = self.wrapped?;
        Some(Self { test: Some(test), post_test: None, exit: Some(test.exit), wrapped: None, ..self })
    }
}

pub(super) struct Layout {
    pub(super) loops: Vec<Option<Loop>>,
    level: Vec<Option<usize>>,
    postdominators: DominanceTree,
    conditional_cases: BTreeMap<usize, Rc<ConditionalCase>>,
    loop_exit_labels: BTreeMap<usize, LoopExitLabel>,
    locals: Option<LocalLiveness>,
}

impl Layout {
    pub(super) fn with_exceptions(
        graph: &ControlFlowGraph,
        instructions: &[Instruction],
        assertions: Option<&Sites>,
        exceptions: &Exceptions,
    ) -> Result<Self, StructureError> {
        Self::with_predicate_cuts(graph, instructions, assertions, exceptions, &[])
    }

    pub(super) fn with_predicate_cuts(
        graph: &ControlFlowGraph,
        instructions: &[Instruction],
        assertions: Option<&Sites>,
        exceptions: &Exceptions,
        cuts: &[super::switch_expression::predicate::Cut],
    ) -> Result<Self, StructureError> {
        let mut immediate_dominators = Some(graph.immediate_dominators());
        let mut natural_loops =
            graph.natural_loops_with_dominators(immediate_dominators.as_deref().unwrap());
        let mut dominators = (natural_loops.len() > 1)
            .then(|| DominanceTree::new(immediate_dominators.take().unwrap()));
        if let Some(dominators) = &dominators {
            // An exit-only tail can contain a loop with a larger cyclic
            // core than its enclosing loop. Classify by dominance, not size.
            natural_loops.sort_unstable_by_key(|shape| dominators.intervals[shape.header].0);
        }
        let mut loops: Vec<Option<Loop>> = vec![None; graph.blocks.len()];
        let mut level: Vec<Option<usize>> = vec![None; graph.blocks.len()];
        let postdominators = DominanceTree::new(graph.immediate_postdominators());
        let mut conditional_cases = BTreeMap::new();
        let mut loop_exit_labels = BTreeMap::new();
        let mut seen_tail = Vec::new();
        let mut pending = Vec::new();
        for natural_loop in natural_loops {
            let header = natural_loop.header;
            let unsupported = || StructureError::Flow {
                offset: instructions[graph.blocks[header].instructions.start].offset,
            };
            let inside = |block: usize| natural_loop.blocks.binary_search(&block).is_ok();
            let parent = level[header];
            if natural_loop
                .blocks
                .iter()
                .any(|&block| level[block] != parent)
            {
                return Err(unsupported());
            }
            let monitor_boundary = exceptions.monitor_finally_boundary(header);
            let label_boundary = exceptions.finally_label_boundary(header);
            let predicate = cuts.iter().find(|cut| cut.owns(header) && !inside(cut.header));
            let outer_transfer = |block| {
                if monitor_boundary == Some(block) || label_boundary == Some(block) {
                    return true;
                }
                if predicate.is_some_and(|cut| cut.outcomes.contains(&block)) {
                    return true;
                }
                let mut enclosing = parent;
                while let Some(head) = enclosing {
                    let shape: Loop = loops[head].expect("outer loops are classified first");
                    if block == head || Some(block) == shape.exit {
                        return true;
                    }
                    enclosing = shape.parent;
                }
                false
            };
            let exits: BTreeSet<_> = natural_loop
                .blocks
                .iter()
                .flat_map(|&block| graph.blocks[block].successors.iter().copied())
                .filter(|&next| !inside(next) && !outer_transfer(next))
                .collect();
            let wrapped = exceptions.finally_wrapped_loop(instructions, graph, &natural_loop);
            let repeating_try = exceptions.repeating_try_at_entry(header);
            let exception_body = wrapped.map(|(arm, ..)| arm).or_else(|| {
                exceptions.loop_finally_regions().find_map(|(region, _)| {
                    (region.start == header && natural_loop.latches.iter().any(|&latch| {
                        !exceptions.contains(Some(region.body), latch)
                    })).then_some(region.body)
                })
            }).or(repeating_try);
            let retry = if exception_body.is_none() {
                exceptions.retry_loop_body(header)
            } else {
                None
            };
            let terminal_retry = retry.is_some_and(|(_, terminal)| terminal);
            let exception_body = exception_body.or(retry.map(|(body, _)| body));
            let mirrored_exit = {
                let mut targets = exceptions
                    .loop_finally_regions()
                    .filter(|(region, _)| inside(region.start))
                    .flat_map(|(_, finally)| finally.branched().unwrap().loop_targets.iter().copied())
                    .filter(|&target| !inside(target) && !outer_transfer(target));
                targets.next().filter(|&exit| targets.all(|target| target == exit))
            };
            let is_failure = |block| assertions.is_some_and(|sites| sites.is_failure_block(block));
            let tests_condition = matches!(instructions[graph.blocks[header].instructions.end - 1].opcode,
                0x99..=0xa6 | 0xc6..=0xc7)
                && !assertions.is_some_and(|sites| sites.starts(header))
                && exception_body.is_none();
            let test = match graph.blocks[header].successors.as_slice() {
                [first, second] if tests_condition => match (inside(*first), inside(*second)) {
                    (true, false) if !outer_transfer(*second) && !is_failure(*second) => {
                        Some(While {
                            body: *first,
                            exit: *second,
                        })
                    }
                    (false, true) if !outer_transfer(*first) && !is_failure(*first) => {
                        Some(While {
                            body: *second,
                            exit: *first,
                        })
                    }
                    _ => None,
                },
                _ => None,
            };
            let post_test = if terminal_retry {
                None
            } else if let Some((_, latch, _, _)) = wrapped {
                Some(PostTest::classify_latch(graph, instructions, &natural_loop, latch)
                    .ok_or_else(unsupported)?)
            } else {
                PostTest::classify(graph, instructions, &natural_loop)
            };
            let conditional_case = if parent.is_none() && predicate.is_none() && post_test.is_none()
                && exits.len() > 1
            {
                test.and_then(|test| ConditionalCase::prove(
                    graph, instructions, exceptions, &natural_loop, test.exit, &exits,
                    |head| postdominators.parent[head],
                ))
            } else {
                None
            };
            let exit_label = if conditional_case.is_none() && parent.is_none() && predicate.is_none()
                && post_test.is_none() && exits.len() > 1
            {
                test.and_then(|test| LoopExitLabel::prove(graph, instructions, &natural_loop, test.exit, &exits))
            } else {
                None
            };
            let external_boundary = |block| {
                conditional_case.as_ref().is_some_and(|case| case.loop_boundary(block))
                    || exit_label.is_some_and(|label| block == label.join)
            };
            // A header that already executes body code can branch to an
            // early method exit. Keep such abrupt tails in the body when
            // the unique conditional latch supplies the normal continuation.
            let post_exit = post_test.map(PostTest::exit).filter(|&candidate| {
                exits.contains(&candidate)
                    && !is_failure(candidate)
                    && level[candidate] == parent
                    && exits.iter().all(|&target| {
                        if target == candidate || is_failure(target) {
                            return true;
                        }
                        let node = &graph.blocks[target];
                        node.successors.is_empty()
                            && node.exception_predecessors.is_empty()
                            && node.predecessors.iter().copied().all(inside)
                            && (node.exception_successors.is_empty() || wrapped.is_some())
                            && matches!(instructions[node.instructions.end - 1].opcode, 0xac..=0xb1 | 0xbf)
                    })
            });
            let mut exit = conditional_case.as_ref().map(|case| case.continuation)
                .or(post_exit).or(mirrored_exit).or_else(|| exceptions.retry_loop_exit(header)).or_else(|| {
                // A repeating try or terminal retry owns even the noncyclic
                // terminal tails of its body; none is a loop exit.
                if repeating_try.is_some() || terminal_retry {
                    return None;
                }
                let mut normal = exits.iter().copied().filter(|&target| !is_failure(target));
                let first = normal.next();
                match (first, normal.next()) {
                    (Some(target), None) => Some(target),
                    (Some(a), Some(b)) => test.map(|test| test.exit).or_else(|| {
                        let common = normal.try_fold(postdominators.common(a, b)?, |a, b| {
                            postdominators.common(a, b)
                        })?;
                        (!inside(common) && !outer_transfer(common) && level[common] == parent)
                            .then_some(common)
                    }),
                    (None, _) => None,
                }
            });

            // A natural loop contains only blocks that can return to its
            // header. Include dominated exit-only tails in the same source
            // loop, stopping at its continuation or an enclosing transfer.
            pending.extend(exits.iter().copied().filter(|&target| Some(target) != exit && !external_boundary(target)));
            if !pending.is_empty() && seen_tail.is_empty() {
                seen_tail.resize(graph.blocks.len(), usize::MAX);
            }
            let mut exit_is_required = false;
            let mut tails = Vec::new();
            while let Some(block) = pending.pop() {
                if Some(block) == exit
                    || inside(block)
                    || outer_transfer(block)
                    || external_boundary(block)
                    || std::mem::replace(&mut seen_tail[block], header) == header
                {
                    continue;
                }
                let dominates = dominators.get_or_insert_with(|| {
                    DominanceTree::new(immediate_dominators.take().unwrap())
                });
                if level[block] != parent {
                    return Err(unsupported());
                }
                if loops[block].is_some() || !dominates.contains(header, block) {
                    if exit_is_required {
                        return Err(unsupported());
                    }
                    if let Some(previous) = exit.replace(block) {
                        pending.push(previous);
                    }
                    exit_is_required = true;
                    continue;
                }
                tails.push(block);
                pending.extend_from_slice(&graph.blocks[block].successors);
            }
            if exit.is_some_and(|block| level[block] != parent) {
                return Err(unsupported());
            }
            if !tails.is_empty() {
                tails.sort_unstable();
                let dominates = dominators.as_ref().expect("tail dominance was tested");
                let enters_tail = |pred| {
                    dominates.contains(0, pred)
                        && !inside(pred)
                        && tails.binary_search(&pred).is_err()
                };
                if tails.iter().any(|&block| {
                    let node = &graph.blocks[block];
                    node.predecessors
                        .iter()
                        .chain(&node.exception_predecessors)
                        .copied()
                        .any(enters_tail)
                }) {
                    return Err(unsupported());
                }
            }
            // If only a catch returns to the test, the tested body is an
            // exit-only tail in the normal-edge natural loop.
            let test = test.or_else(|| {
                let exit = exit?;
                if !tests_condition
                    || tails.is_empty()
                    || !natural_loop
                        .latches
                        .contains(&exceptions.handler_latch(header, exit)?)
                {
                    return None;
                }
                let &[first, second] = graph.blocks[header].successors.as_slice() else {
                    return None;
                };
                let body = if first == exit {
                    second
                } else if second == exit {
                    first
                } else {
                    return None;
                };
                tails.binary_search(&body).ok().map(|_| While { body, exit })
            });
            for block in natural_loop.blocks.into_iter().chain(tails) {
                // Keep the header visible as one node of the parent region,
                // including while classifying a later sibling loop.
                if block != header {
                    level[block] = Some(header);
                }
            }
            loops[header] = Some(Loop {
                test: test.filter(|test| Some(test.exit) == exit),
                post_test: post_test.filter(|test| Some(test.exit()) == exit),
                exit,
                exception_body,
                wrapped: wrapped.map(|(_, _, body, exit)| While { body, exit }),
                parent,
            });
            if let Some(case) = conditional_case {
                conditional_cases.insert(case.head, Rc::new(case));
            }
            if let Some(label) = exit_label {
                loop_exit_labels.insert(header, label);
            }
        }
        // An abrupt arm can put only part of an exceptional cleanup in
        // the natural loop. All its arms are lexically at the try's level.
        for (region, finally) in exceptions.loop_finally_regions() {
            let at_header = loops[region.start].is_some_and(|shape| shape.exception_body == Some(region.body));
            let owner = if at_header { Some(region.start) } else { level[region.start] };
            for block in exceptions.arm_blocks(finally.arm) {
                if level[block].is_some_and(|head| exceptions.contains(Some(finally.arm), head)) {
                    continue;
                }
                level[block] = owner;
                if let Some(shape) = &mut loops[block] {
                    shape.parent = owner;
                }
            }
        }
        Ok(Self {
            loops,
            level,
            postdominators,
            conditional_cases,
            loop_exit_labels,
            locals: None,
        })
    }

    pub(super) fn cut_at_cycle_entry(&mut self, graph: &ControlFlowGraph, header: usize) {
        self.postdominators = DominanceTree::new(graph.immediate_postdominators_at_cut(header));
    }

    pub(super) fn conditional_case(&self, block: usize) -> Option<Rc<ConditionalCase>> {
        self.conditional_cases.get(&block).cloned()
    }

    pub(super) fn loop_exit_label(&self, block: usize) -> Option<LoopExitLabel> {
        self.loop_exit_labels.get(&block).copied()
    }

    pub(super) fn install_closed_cycle(&mut self, header: usize, members: &[bool]) {
        for (block, level) in self.level.iter_mut().enumerate() {
            if block != header && members[block] {
                *level = Some(header);
            }
        }
        self.loops[header] = Some(Loop {
            test: None,
            post_test: None,
            exit: None,
            exception_body: None,
            wrapped: None,
            parent: None,
        });
    }

    pub(super) fn inside(&self, block: usize, region: Region<'_, '_, '_>) -> bool {
        self.containing_loop(block) == region.layout_loop_header && !region.has_stop(block)
    }

    pub(super) fn containing_loop(&self, block: usize) -> Option<usize> {
        self.level[block]
    }

    pub(super) fn direct_loop_member(&self, block: usize, header: usize) -> bool {
        self.level[block] == Some(header)
    }

    pub(super) fn normal_join(&self, head: usize, region: Region<'_, '_, '_>) -> Option<usize> {
        // Like DomHelper, prefer the nearest common postdominator but never
        // cross a boundary set by the enclosing structured statement.
        let join = self.postdominators.parent[head]?;
        if region.stop == Some(join) {
            return Some(join);
        }
        if !self.inside(join, region)
            || region
                .stop
                .is_some_and(|stop| self.postdominators.contains(join, stop))
        {
            return None;
        }
        Some(join)
    }

    pub(super) fn can_fall_through(&self, from: usize, next: usize, join: Option<usize>) -> bool {
        join != Some(from)
            && !join.is_some_and(|join| self.postdominators.contains(next, join))
            && self.postdominators.contains(next, from)
    }

    pub(super) fn common_join(
        &self,
        graph: &ControlFlowGraph,
        region: Region<'_, '_, '_>,
        arms: impl IntoIterator<Item = (usize, Option<usize>)>,
    ) -> Option<usize> {
        // An early return can hide a normal join from plain postdominance.
        // Propose a shared continuation; emission still verifies that the
        // resulting arm regions are disjoint and finish at that continuation
        // or an explicit terminal statement.
        let mut seen = vec![usize::MAX; graph.blocks.len()];
        let mut queue = VecDeque::new();
        for (start, fallthrough) in arms {
            if !self.inside(start, region) {
                continue;
            }
            queue.push_back(start);
            while let Some(block) = queue.pop_front() {
                if seen[block] == start {
                    continue;
                }
                if seen[block] != usize::MAX {
                    return Some(block);
                }
                seen[block] = start;
                let successors = match &self.loops[block] {
                    Some(loop_shape) => loop_shape.exit.as_slice(),
                    None => &graph.blocks[block].successors,
                };
                queue.extend(successors.iter().copied().filter(|&next| {
                    Some(next) != fallthrough && self.inside(next, region) && seen[next] != start
                }));
            }
        }
        None
    }

    pub(super) fn local_is_live(
        &mut self,
        graph: &ControlFlowGraph,
        instructions: &[Instruction],
        block: usize,
        slot: u16,
    ) -> bool {
        self.locals
            .get_or_insert_with(|| LocalLiveness::new(graph, instructions))
            .is_live(graph, block, slot)
    }
}

/// Used only for slots whose incoming bindings differ. A local is live at a
/// join if some path reads it before the next write. Exception edges see the
/// incoming state conservatively: a throwable instruction can precede a store
/// in the same block.
struct LocalLiveness {
    accesses: Vec<Vec<(u16, bool)>>,
    seen: Vec<usize>,
    pending: Vec<usize>,
    generation: usize,
}

impl LocalLiveness {
    fn new(graph: &ControlFlowGraph, instructions: &[Instruction]) -> Self {
        let accesses = graph
            .blocks
            .iter()
            .map(|block| {
                let mut first = BTreeMap::new();
                for instruction in &instructions[block.instructions.clone()] {
                    let (slot, read, wide) = match (instruction.opcode, &instruction.operand) {
                        (0x15..=0x19, Operand::Local(slot)) => (*slot, true, false),
                        (op @ 0x1a..=0x2d, _) => (u16::from((op - 0x1a) % 4), true, false),
                        (op @ 0x36..=0x3a, Operand::Local(slot)) => {
                            (*slot, false, matches!(op, 0x37 | 0x39))
                        }
                        (op @ 0x3b..=0x4e, _) => (
                            u16::from((op - 0x3b) % 4),
                            false,
                            matches!((op - 0x3b) / 4, 1 | 3),
                        ),
                        (0x84, Operand::Increment { index, .. }) => (*index, true, false),
                        _ => continue,
                    };
                    first.entry(slot).or_insert(read);
                    if !read
                        && wide
                        && let Some(high) = slot.checked_add(1)
                    {
                        first.entry(high).or_insert(false);
                    }
                }
                first.into_iter().collect()
            })
            .collect();
        Self {
            accesses,
            seen: vec![0; graph.blocks.len()],
            pending: Vec::new(),
            generation: 0,
        }
    }

    fn is_live(&mut self, graph: &ControlFlowGraph, block: usize, slot: u16) -> bool {
        if self.generation == usize::MAX {
            self.seen.fill(0);
            self.generation = 0;
        }
        self.generation += 1;
        self.pending.clear();
        self.pending.push(block);
        while let Some(block) = self.pending.pop() {
            if std::mem::replace(&mut self.seen[block], self.generation) == self.generation {
                continue;
            }
            let node = &graph.blocks[block];
            let accesses = &self.accesses[block];
            match accesses.binary_search_by_key(&slot, |&(slot, _)| slot) {
                Ok(index) if accesses[index].1 => return true,
                Ok(_) => {}
                Err(_) => self.pending.extend_from_slice(&node.successors),
            }
            self.pending.extend_from_slice(&node.exception_successors);
        }
        false
    }
}

struct DominanceTree {
    parent: Vec<Option<usize>>,
    intervals: Vec<(usize, usize)>,
}

impl DominanceTree {
    fn new(parent: Vec<Option<usize>>) -> Self {
        // Number the forest in preorder beneath a virtual root so dominance
        // is a single subtree interval lookup.
        let root = parent.len();
        let mut first_child = vec![None; root + 1];
        let mut next_sibling = vec![None; root];
        for (block, &parent) in parent.iter().enumerate() {
            next_sibling[block] = first_child[parent.unwrap_or(root)].replace(block);
        }
        let mut intervals = vec![(0, 0); root];
        let mut next_index = 0;
        let mut dfs = vec![(root, first_child[root])];
        while let Some((node, child)) = dfs.last_mut() {
            if let Some(block) = *child {
                *child = next_sibling[block];
                intervals[block].0 = next_index;
                next_index += 1;
                dfs.push((block, first_child[block]));
            } else {
                if *node != root {
                    intervals[*node].1 = next_index;
                }
                dfs.pop();
            }
        }
        Self { parent, intervals }
    }

    fn contains(&self, parent: usize, node: usize) -> bool {
        let (start, end) = self.intervals[parent];
        (start..end).contains(&self.intervals[node].0)
    }

    fn common(&self, mut a: usize, b: usize) -> Option<usize> {
        loop {
            if self.contains(a, b) {
                return Some(a);
            }
            a = self.parent[a]?;
        }
    }
}
