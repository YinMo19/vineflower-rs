// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use std::collections::btree_map::Entry;
use std::collections::{BTreeMap, BTreeSet};
use std::ops::Range;

use crate::bytecode::{Instruction, Operand};
use crate::cfg::ControlFlowGraph;

use super::cleanup_locals;
use super::monitor::{MonitorCandidates, MonitorPlan};
use super::{
    Dominance, MonitorDeparture, Route, local_access, local_touches, normal_exits, reference_load,
    reference_store,
};

pub(super) enum NormalCopies<'a> {
    Ordinary(&'a [Route]),
    OverrideVoid { handler: usize },
}

pub(in crate::structure) struct BranchedFinally {
    pub(in crate::structure) entry: usize,
    pub(in crate::structure) continuation: Option<usize>,
    pub(in crate::structure) removed: BTreeSet<usize>,
    pub(super) blocks: BTreeSet<usize>,
    pub(super) body_join: Option<usize>,
    pub(super) projected_entries: BTreeSet<usize>,
    pub(super) empty_catches: BTreeSet<usize>,
    pub(in crate::structure) forced_return: Option<usize>,
    pub(super) returns: Vec<ReturnResume>,
    pub(in crate::structure) label: Option<LabelResume>,
    pub(super) prefix_block: Option<usize>,
    pub(in crate::structure) tail: Option<usize>,
    pub(super) tail_code: Range<usize>,
    pub(in crate::structure) monitor_exit: Option<FinallyMonitorExit>,
    pub(in crate::structure) shared_return: Option<SharedReturn>,
    pub(in crate::structure) loop_targets: BTreeSet<usize>,
    pub(super) nested_handlers: BTreeMap<usize, NestedHandler>,
    pub(super) copied_routes: BTreeSet<Route>,
}

pub(super) enum NestedHandler {
    Catch,
    Finally(NestedFinally),
}

pub(super) struct NestedFinally {
    block: usize,
    code: Range<usize>,
}

impl NestedFinally {
    /// Compare the cleanup, not the compiler's private store/rethrow pair.
    /// An isolated, optionally self-protected store is not a throwing block.
    fn prove(
        instructions: &[Instruction],
        graph: &ControlFlowGraph,
        routes: &[Vec<Route>],
        handler: usize,
    ) -> Option<Self> {
        let entry = &graph.blocks[handler];
        let store = &instructions[entry.instructions.start];
        let slot = reference_store(store)?;
        let binding = cleanup_locals::binding_slot(store)?;
        let (block, start) = if entry.instructions.len() == 1 {
            let &[next] = entry.successors.as_slice() else { return None; };
            let body = &graph.blocks[next];
            if body.predecessors != [handler]
                || !body.exception_predecessors.is_empty()
                || !routes[handler].is_empty()
            {
                return None;
            }
            (next, body.instructions.start)
        } else {
            (handler, entry.instructions.start + 1)
        };
        let body = &graph.blocks[block];
        let [code @ .., load, throw] = &instructions[start..body.instructions.end] else {
            return None;
        };
        if reference_load(load) != Some(slot)
            || throw.opcode != 0xbf
            || code.iter().any(|op| local_touches(op, slot))
            || body.exception_successors.contains(&handler)
            || (!body.exception_successors.is_empty()
                && cleanup_locals::live_at_any(
                    instructions, graph, body.exception_successors.iter().copied(), binding,
                ))
        {
            return None;
        }
        Some(Self { block, code: start..start + code.len() })
    }
}

pub(in crate::structure) struct FinallyMonitorExit {
    pub(in crate::structure) acquisition: usize,
    pub(in crate::structure) edge: MonitorDeparture,
    pub(super) copy: usize,
}

#[derive(Clone, Copy)]
pub(in crate::structure) struct SharedReturn {
    pub(in crate::structure) block: usize,
    pub(in crate::structure) jump: usize,
}

/// One normal cleanup copy resumes a break to an enclosing labeled block.
/// The other continues to the loop condition; the cleanup's own break
/// overrides both and exits only the loop.
pub(in crate::structure) struct LabelResume {
    pub(in crate::structure) entry: usize,
    pub(in crate::structure) target: usize,
    pub(in crate::structure) jump: usize,
    pub(in crate::structure) loop_exit: usize,
    pub(in crate::structure) locals: Vec<LabelLocal>,
}

pub(in crate::structure) struct LabelLocal {
    pub(in crate::structure) slot: u16,
    pub(in crate::structure) store: usize,
    pub(in crate::structure) from_finally: bool,
}

impl LabelResume {
    fn prove(
        instructions: &[Instruction],
        graph: &ControlFlowGraph,
        routes: &[Vec<Route>],
        body: &BTreeSet<usize>,
        dominance: &Dominance,
        branch: &BranchedFinally,
        entries: &BTreeMap<usize, Option<usize>>,
    ) -> Option<Self> {
        if entries.len() != 2
            || branch.loop_targets.len() != 1
            || !branch.returns.is_empty()
            || !branch.tail_code.is_empty()
            || !branch.nested_handlers.is_empty()
            || branch.shared_return.is_some()
            || branch.monitor_exit.is_some()
        {
            return None;
        }
        let tail = branch.tail?;
        let &loop_exit = branch.loop_targets.first()?;
        let &header = body.first()?;
        let shape = dominance.natural_loops(graph).iter().find(|shape| shape.header == header)?;
        let &[latch] = shape.latches.as_slice() else { return None };
        let test = &graph.blocks[latch];
        if test.successors.len() != 2
            || !test.successors.contains(&header)
            || !test.successors.contains(&loop_exit)
            || !super::super::do_while::is_conditional(instructions[test.instructions.end - 1].opcode)
            || entries.values().filter(|&&target| target == Some(latch)).count() != 1
        {
            return None;
        }
        let (&entry, &target) = entries.iter().find(|&(_, &target)| target != Some(latch))?;
        let target = target?;
        if target <= loop_exit {
            return None;
        }
        for end in [loop_exit, target] {
            let node = &graph.blocks[end];
            if !node.successors.is_empty()
                || !node.exception_predecessors.is_empty()
                || !routes[end].is_empty()
                || !matches!(instructions[node.instructions.end - 1].opcode, 0xac..=0xb1)
            {
                return None;
            }
        }
        let exit = &graph.blocks[loop_exit];
        if exit.predecessors.iter().any(|pred| {
            *pred != latch && !branch.blocks.contains(pred) && !branch.removed.contains(pred)
        }) {
            return None;
        }
        let target_node = &graph.blocks[target];
        let &[source] = target_node.predecessors.as_slice() else { return None };
        let &[origin] = graph.blocks[entry].predecessors.as_slice() else { return None };
        if !branch.removed.contains(&source)
            || !body.contains(&origin)
            || graph.blocks[origin].successors != [entry]
        {
            return None;
        }

        let read_slots: BTreeSet<_> = instructions[target_node.instructions.clone()]
            .iter()
            .filter(|op| matches!(op.opcode, 0x15 | 0x1a..=0x1d))
            .filter_map(local_access)
            .collect();
        let mut locals = Vec::new();
        for slot in read_slots {
            // Values transferred out of these scopes may only be observed at
            // the label. Prove a single writer before the pending break, or
            // a writer that dominates completion of the canonical finally.
            let mut prior = None;
            let mut cleanup = None;
            let mut copies = 0;
            let mut observed_elsewhere = false;
            for (block, node) in graph.blocks.iter().enumerate() {
                if block == target { continue; }
                for index in node.instructions.clone() {
                    let op = &instructions[index];
                    if !local_touches(op, slot) { continue; }
                    if !matches!(op.opcode, 0x36 | 0x3b..=0x3e) {
                        observed_elsewhere = true;
                        continue;
                    }
                    if block == origin && prior.is_none() {
                        prior = Some(index);
                    } else if branch.blocks.contains(&block) && cleanup.is_none()
                        && dominance.contains(block, tail)
                    {
                        cleanup = Some(index);
                    } else if branch.removed.contains(&block) {
                        copies += 1;
                    } else {
                        return None;
                    }
                }
            }
            match (prior, cleanup, copies) {
                (Some(store), None, 0) if !observed_elsewhere => {
                    locals.push(LabelLocal { slot, store, from_finally: false });
                }
                (None, Some(store), 2) if !observed_elsewhere => {
                    locals.push(LabelLocal { slot, store, from_finally: true });
                }
                (None, None, 0) => {}
                _ => return None,
            }
        }
        if !locals.iter().any(|local| local.from_finally) {
            return None;
        }
        let jump = graph.blocks[source].instructions.end - 1;
        Some(Self { entry, target, jump, loop_exit, locals })
    }
}

pub(super) struct ReturnResume {
    pub(super) entry: usize,
    pub(super) block: usize,
    pub(super) spill: Option<(usize, usize)>,
}

impl ReturnResume {
    fn prove(
        instructions: &[Instruction],
        graph: &ControlFlowGraph,
        routes: &[Vec<Route>],
        entry: usize,
        block: usize,
        prefix: usize,
        copy: &BTreeSet<usize>,
        targets: &BTreeSet<usize>,
    ) -> Option<Self> {
        let node = &graph.blocks[block];
        if !node.exception_predecessors.is_empty()
            || !node.predecessors.iter().all(|pred| copy.contains(pred))
        {
            return None;
        }
        let load = node.instructions.start + prefix;
        let spill = match &instructions[load..node.instructions.end] {
            [Instruction { opcode: 0xb1, .. }] => None,
            [reload, transfer] => {
                let local = cleanup_locals::returned(reload, transfer)?;
                let entry = &graph.blocks[entry];
                let &[pred] = entry.predecessors.as_slice() else {
                    return None;
                };
                let origin = &graph.blocks[pred];
                let store = origin.instructions.end - 1;
                if origin.instructions.end != entry.instructions.start
                    || cleanup_locals::store(&instructions[store]) != Some(local)
                    || !routes[block].is_empty()
                    || copy.iter().any(|&block| !routes[block].is_empty())
                    || cleanup_locals::live_at_any(instructions, graph, targets.iter().copied(), local)
                    || instructions[node.instructions.start..load].iter().any(|op| local.touches(op))
                    || copy.iter().any(|&block| {
                        instructions[graph.blocks[block].instructions.clone()].iter().any(|op| local.touches(op))
                    })
                {
                    return None;
                }
                Some((load, store))
            }
            _ => return None,
        };
        Some(Self { entry, block, spill })
    }
}

impl BranchedFinally {
    /// Mirrors the exceptional cleanup against its normal copies. An edge
    /// leaving both copies must agree on its exact destination; only a
    /// rethrow of the original exception can resume the normal path instead.
    pub(super) fn prove(
        instructions: &[Instruction],
        graph: &ControlFlowGraph,
        routes: &[Vec<Route>],
        body: &BTreeSet<usize>,
        handler: usize,
        monitors: &MonitorCandidates<'_>,
        dominance: &Dominance,
        normal: NormalCopies<'_>,
    ) -> Option<Self> {
        let start = &graph.blocks[handler];
        if handler == 0 || !start.predecessors.is_empty() || body.contains(&handler) {
            return None;
        }
        let slot = reference_store(&instructions[start.instructions.start])?;
        let entry = if start.instructions.len() == 1 {
            let &[next] = start.successors.as_slice() else {
                return None;
            };
            if graph.blocks[next].predecessors != [handler] {
                return None;
            }
            next
        } else {
            handler
        };
        let monitor = monitors.get(&entry).map(|&(plan, _)| plan);
        let enclosing = monitors
            .values()
            .copied()
            .filter(|(_, covered)| {
                covered.binary_search(&handler).is_ok()
                    && body.iter().all(|block| covered.binary_search(block).is_ok())
            })
            .min_by_key(|(_, covered)| covered.len());
        let mut monitor_exit = None;
        let mut cleanup = BTreeSet::new();
        let mut rethrow = None;
        let mut boundary = BTreeSet::new();
        let mut nested_handlers = BTreeMap::new();
        let mut pending = vec![entry];
        while let Some(index) = pending.pop() {
            if !dominance.contains(handler, index) {
                boundary.insert(index);
                continue;
            }
            if !cleanup.insert(index) {
                continue;
            }
            let block = &graph.blocks[index];
            if body.contains(&index) {
                return None;
            }
            if monitor.is_none() {
                for &route in &routes[index] {
                    if route.handler != handler && dominance.contains(handler, route.handler) {
                        let is_finally = route.catch_type == 0;
                        match nested_handlers.entry(route.handler) {
                            Entry::Occupied(kind) => {
                                if matches!(kind.get(), NestedHandler::Finally(_)) != is_finally {
                                    return None;
                                }
                            }
                            Entry::Vacant(kind) => {
                                let proof = if is_finally {
                                    NestedHandler::Finally(NestedFinally::prove(
                                        instructions, graph, routes, route.handler,
                                    )?)
                                } else {
                                    NestedHandler::Catch
                                };
                                kind.insert(proof);
                            }
                        }
                        pending.push(route.handler);
                    }
                }
            }
            let start = block.instructions.start + usize::from(index == handler);
            let mut end = block.instructions.end;
            if let [.., load, throw] = &instructions[start..end]
                && reference_load(load) == Some(slot)
                && throw.opcode == 0xbf
            {
                end -= 2;
                if rethrow.replace((index, start..end)).is_some() {
                    return None;
                }
            }
            if instructions[start..end]
                .iter()
                .any(|op| local_touches(op, slot))
            {
                return None;
            }
            if let Some((owner, covered)) = enclosing
                && let Some(target) = owner.unlock_target(instructions, graph, index)
            {
                if target <= index
                    || covered.binary_search(&target).is_ok()
                    || monitor_exit.replace(MonitorDeparture { source: index, target }).is_some()
                {
                    return None;
                }
                continue;
            }
            pending.extend(block.successors.iter().copied());
        }
        if cleanup.iter().any(|&index| {
            let block = &graph.blocks[index];
            if nested_handlers.contains_key(&index) {
                !block.predecessors.is_empty()
                    || block.exception_predecessors.iter().any(|pred| !cleanup.contains(pred))
            } else {
                index != handler && !block.exception_predecessors.is_empty()
            }
        }) {
            return None;
        }
        let (tail, tail_code) = rethrow.map_or((None, 0..0), |(tail, code)| (Some(tail), code));
        if tail == Some(entry) {
            return None;
        }
        cleanup.insert(handler);
        if let Some(monitor) = monitor {
            for block in monitor.handler_blocks() {
                if body.contains(&block)
                    || !cleanup.insert(block)
                    || instructions[graph.blocks[block].instructions.clone()]
                        .iter()
                        .any(|op| local_touches(op, slot))
                {
                    return None;
                }
            }
            if monitor.handler_blocks().any(|block| {
                graph.blocks[block]
                    .exception_predecessors
                    .iter()
                    .any(|pred| !cleanup.contains(pred))
            }) {
                return None;
            }
        }
        let mut shared_return = None;
        let mut loop_targets = BTreeSet::new();
        for block in boundary {
            if graph.blocks[block].exception_predecessors.is_empty()
                && dominance.natural_loops(graph).iter().any(|shape| {
                    let inside = |node| shape.blocks.binary_search(&node).is_ok();
                    if !body.iter().copied().any(inside)
                        || !body.iter().copied().all(|member| dominance.contains(shape.header, member))
                    {
                        return false;
                    }
                    if block == shape.header {
                        return true;
                    }
                    if inside(block) {
                        // A shared update belongs to the for header, not to
                        // either cleanup. Emission must prove that for loop.
                        let node = &graph.blocks[block];
                        return matches!(&instructions[node.instructions.clone()],
                            [update, jump] if matches!(update.operand, Operand::Increment { .. })
                                && matches!(jump.opcode, 0xa7 | 0xc8))
                            && node.successors == [shape.header];
                    }
                    // A break can leave through a noncyclic tail of the
                    // normal copy rather than directly from the loop core.
                    dominance.contains(shape.header, block)
                })
            {
                loop_targets.insert(block);
                continue;
            }

            // Outside a loop, keep the existing proof for a private,
            // terminal return shared by exactly one pair of copies.
            let node = &graph.blocks[block];
            let &[sample, source] = node.predecessors.as_slice() else {
                return None;
            };
            if shared_return.is_some()
                || monitor.is_some()
                || enclosing.is_some()
                || tail.is_none_or(|tail| block <= tail)
                || sample >= handler
                || cleanup.contains(&sample)
                || !cleanup.contains(&source)
                || source >= block
                || !node.exception_predecessors.is_empty()
                || !routes[block].is_empty()
                || !matches!(instructions[node.instructions.end - 1].opcode, 0xac..=0xb1)
                || instructions[node.instructions.clone()].iter().any(|op| local_touches(op, slot))
            {
                return None;
            }
            let jump = explicit_jump(instructions, graph, source, block)?;
            explicit_jump(instructions, graph, sample, block)?;
            if !routes[source].is_empty() || !routes[sample].is_empty() {
                return None;
            }
            shared_return = Some(SharedReturn { block, jump });
            cleanup.insert(block);
        }
        if cleanup.iter().any(|&block| {
            Some(block) != shared_return.map(|exit| exit.block)
                && graph.blocks[block].predecessors.iter().any(|pred| !cleanup.contains(pred))
        }) {
            return None;
        }
        if !loop_targets.is_empty() && instructions.iter().enumerate().any(|(index, op)| {
            (tail.is_none() || index != tail_code.end) && cleanup_locals::reads(op, slot)
        }) {
            return None;
        }
        if body.iter().any(|&block| {
            matches!(
                instructions[graph.blocks[block].instructions.end - 1].opcode,
                0xac..=0xb1
            )
        }) {
            return None;
        }
        let exits: BTreeSet<_> = normal_exits(graph, body).collect();
        if shared_return.is_some() && exits.len() != 1 {
            return None;
        }
        let projection = monitor_exit.zip(enclosing.map(|(owner, _)| owner));
        if let Some((edge, _)) = projection
            && (exits.len() != 1
                || cleanup.contains(&edge.target)
                || graph.blocks[entry].successors.len() != 2
                || tail.is_none_or(|tail| !graph.blocks[entry].successors.contains(&tail)))
        {
            return None;
        }
        let mut result = Self {
            entry,
            continuation: None,
            removed: BTreeSet::new(),
            blocks: cleanup,
            body_join: None,
            projected_entries: BTreeSet::new(),
            empty_catches: BTreeSet::new(),
            forced_return: None,
            returns: Vec::new(),
            label: None,
            prefix_block: None,
            tail,
            tail_code,
            monitor_exit: None,
            shared_return,
            loop_targets,
            nested_handlers,
            copied_routes: BTreeSet::new(),
        };
        let mut continuing = BTreeMap::new();
        for &sample in &exits {
            let pair = match (monitor, monitors.get(&sample).map(|&(plan, _)| plan)) {
                (Some(pattern), Some(sample)) => Some(MonitorCopy { pattern, sample }),
                (None, None) => None,
                _ => return None,
            };
            let (tail, removed, copied_exit, copied_routes) = result.match_copy(
                instructions, graph, routes, body, handler, sample, None, pair, projection,
            )?;
            result.copied_routes.extend(copied_routes);
            if let Some((edge, owner)) = projection {
                result.monitor_exit = Some(FinallyMonitorExit {
                    acquisition: owner.acquisition,
                    edge,
                    copy: copied_exit?,
                });
            }
            let direct_return = exits.len() == 1
                && monitor.is_none()
                && result.nested_handlers.is_empty()
                && result.tail.is_some();
            let loop_return = exits.len() > 1 && !result.loop_targets.is_empty();
            // A single normal cleanup path can still originate from a
            // source return. Require its saved value to distinguish that
            // case from a void return after the entire try statement.
            if (direct_return || loop_return)
                && result.shared_return.is_none() && result.monitor_exit.is_none()
                && let Some(block) = tail
                && let Some(resume) = ReturnResume::prove(
                    instructions, graph, routes, sample, block, result.tail_code.len(),
                    &removed, &result.loop_targets,
                )
                && (loop_return || resume.spill.is_some())
            {
                result.returns.push(resume);
            } else {
                continuing.insert(sample, tail);
            }
            for block in removed {
                if !result.removed.insert(block) {
                    return None;
                }
            }
        }
        if let NormalCopies::OverrideVoid { handler } = normal {
            result.resume_overriding_void(instructions, graph, routes, handler, continuing)?;
            return Some(result);
        }
        if let NormalCopies::Ordinary(handlers) = normal
            && monitor.is_none()
            && projection.is_none()
            && result.tail.is_some()
            && result.tail_code.is_empty()
            && result.loop_targets.is_empty()
            && result.shared_return.is_none()
            && result.nested_handlers.is_empty()
            && !continuing.is_empty()
        {
            for route in handlers.iter().filter(|route| route.catch_type != 0) {
                let sample = route.handler;
                let node = &graph.blocks[sample];
                if result.empty_catches.contains(&sample)
                    || body.contains(&sample)
                    || !node.predecessors.is_empty()
                    || node.exception_predecessors.iter().any(|pred| !body.contains(pred))
                {
                    continue;
                }
                let Some(binding) = cleanup_locals::binding_slot(&instructions[node.instructions.start])
                else { continue; };
                let Some((Some(tail), removed, _, _)) = result.match_copy(
                    instructions, graph, routes, body, handler, sample, Some(binding), None, None,
                ) else { continue; };
                if continuing.values().any(|&other| {
                    other != Some(tail)
                        && other.and_then(|block| goto_only(instructions, graph, block))
                            .is_none_or(|next| Some(next) != goto_only(instructions, graph, tail))
                }) || !removed.is_disjoint(&result.removed) {
                    continue;
                }
                result.empty_catches.insert(sample);
                result.removed.extend(removed);
                continuing.insert(sample, Some(tail));
            }
        }
        result.label = LabelResume::prove(
            instructions, graph, routes, body, dominance, &result, &continuing,
        );
        if let Some(label) = &result.label {
            continuing.remove(&label.entry);
        }
        let mut tails: BTreeSet<_> = continuing.values().flatten().copied().collect();
        if !result.tail_code.is_empty()
            && tails.iter().any(|&tail| {
                graph.blocks[tail]
                    .predecessors
                    .iter()
                    .any(|pred| !result.removed.contains(pred))
            })
        {
            return None;
        }
        if tails.len() == 1 {
            let tail = tails.pop_first()?;
            result.continuation = Some(tail);
            result.prefix_block = Some(tail);
        } else if !tails.is_empty() {
            // Distinct final blocks can still finish at the same source
            // continuation, with separate goto stubs from the inliner.
            let mut continuation = None;
            for tail in tails {
                let node = &graph.blocks[tail];
                let &[next] = node.successors.as_slice() else {
                    return None;
                };
                let start = node.instructions.start + result.tail_code.len();
                let [jump] = &instructions[start..node.instructions.end] else {
                    return None;
                };
                if !matches!(jump.opcode, 0xa7 | 0xc8)
                    || !node.exception_predecessors.is_empty()
                    || node
                        .predecessors
                        .iter()
                        .any(|pred| !result.removed.contains(pred))
                    || continuation.is_some_and(|target| target != next)
                {
                    return None;
                }
                continuation = Some(next);
                if !result.removed.insert(tail) {
                    return None;
                }
            }
            result.continuation = continuation;
        }
        if result
            .continuation
            .is_some_and(|next| result.removed.contains(&next))
        {
            return None;
        }
        if exits.len() + result.empty_catches.len() > 1 {
            result.body_join = result.continuation.or_else(|| continuing.first_key_value().map(|(&entry, _)| entry));
            result.projected_entries = continuing.into_keys().collect();
        } else {
            result.body_join = continuing.first_key_value().map(|(&entry, _)| entry);
        }
        Some(result)
    }

    fn match_copy(
        &self,
        instructions: &[Instruction],
        graph: &ControlFlowGraph,
        routes: &[Vec<Route>],
        body: &BTreeSet<usize>,
        handler: usize,
        sample_start: usize,
        sample_binding: Option<cleanup_locals::Local>,
        monitor: Option<MonitorCopy<'_>>,
        departure: Option<(MonitorDeparture, &MonitorPlan)>,
    ) -> Option<(Option<usize>, BTreeSet<usize>, Option<usize>, BTreeSet<Route>)> {
        let mut paired = BTreeMap::new();
        let mut copies = BTreeSet::new();
        let mut removed = BTreeSet::new();
        let mut continuation = None;
        let mut copied_routes = BTreeSet::new();
        let mut renamed = BTreeSet::new();
        let can_rename = monitor.is_none() && departure.is_none() && self.nested_handlers.is_empty();
        let mut local_renames = cleanup_locals::Renames::default();
        let empty_tail = self.tail.filter(|_| {
            self.tail_code.is_empty()
                && self
                    .nested_handlers
                    .values()
                    .any(|kind| matches!(kind, NestedHandler::Finally(_)))
        });
        let mut pending = vec![(self.entry, sample_start)];
        while let Some((mut pattern, mut sample)) = pending.pop() {
            if let Some(tail) = empty_tail {
                // A nested finally can leave a private goto after its inline
                // cleanup in only one copy, before the outer cleanup resumes.
                let mut endpoint = pattern;
                while self.blocks.contains(&endpoint)
                    && let Some(next) = private_forward_goto(instructions, graph, routes, endpoint)
                {
                    endpoint = next;
                }
                if endpoint == tail {
                    pattern = tail;
                    while sample != sample_start
                        && let Some(next) = private_forward_goto(instructions, graph, routes, sample)
                    {
                        if self.blocks.contains(&sample) || body.contains(&sample)
                            || !copies.insert(sample)
                        {
                            return None;
                        }
                        removed.insert(sample);
                        sample = next;
                    }
                }
            }
            if self.loop_targets.contains(&pattern)
                || self.shared_return.is_some_and(|exit| exit.block == pattern)
            {
                if pattern != sample {
                    return None;
                }
                continue;
            }
            if let Some(&previous) = paired.get(&pattern) {
                if previous != sample {
                    return None;
                }
                continue;
            }
            if !copies.insert(sample) || self.blocks.contains(&sample) || body.contains(&sample) {
                return None;
            }
            paired.insert(pattern, sample);
            let nested = self.nested_handlers.get(&pattern);
            let (pattern_block, sample_block, rethrows) =
                if let Some(NestedHandler::Finally(expected)) = nested {
                    let actual = NestedFinally::prove(instructions, graph, routes, sample)?;
                    if actual.block != sample {
                        if self.blocks.contains(&actual.block)
                            || body.contains(&actual.block)
                            || !copies.insert(actual.block)
                        {
                            return None;
                        }
                        removed.insert(sample);
                    }
                    (
                        expected.block,
                        actual.block,
                        Some((expected.code.clone(), actual.code)),
                    )
                } else {
                    (pattern, sample, None)
                };
            let expected = &graph.blocks[pattern_block];
            let actual = &graph.blocks[sample_block];
            let trim = Some(pattern) == self.tail;
            if !trim || !self.tail_code.is_empty() {
                if (nested.is_none()
                    && !(sample == sample_start && sample_binding.is_some())
                    && !actual.exception_predecessors.is_empty())
                    || (nested.is_some() && !graph.blocks[sample].predecessors.is_empty())
                    || routes[pattern_block].len() != routes[sample_block].len()
                {
                    return None;
                }
                for (&expected, &actual) in routes[pattern_block].iter().zip(&routes[sample_block]) {
                    if self.nested_handlers.contains_key(&expected.handler) {
                        if expected.catch_type != actual.catch_type || expected.handler == actual.handler {
                            return None;
                        }
                        pending.push((expected.handler, actual.handler));
                        copied_routes.insert(actual);
                    } else if !same_dispatch(&[expected], &[actual], monitor) {
                        return None;
                    }
                }
            }
            let (mut expected_code, mut actual_code) = if let Some((expected, actual)) = rethrows {
                (&instructions[expected], &instructions[actual])
            } else {
                let start = expected.instructions.start
                    + usize::from(pattern == handler || nested.is_some());
                let actual_start = actual.instructions.start
                    + usize::from(nested.is_some() || (sample == sample_start && sample_binding.is_some()));
                if matches!(nested, Some(NestedHandler::Catch)) {
                    let left = reference_store(&instructions[expected.instructions.start])?;
                    let right = reference_store(&instructions[actual.instructions.start])?;
                    if left != right {
                        renamed.extend([left, right]);
                    }
                }
                let end = if trim { self.tail_code.end } else { expected.instructions.end };
                (&instructions[start..end], &instructions[actual_start..actual.instructions.end])
            };
            if !trim && expected.successors.len() == 1 && actual.successors.len() == 1 {
                // An inlined cleanup can jump over the exception handler
                // where the handler's copy simply falls through. The
                // successor pairing below proves the corresponding target.
                expected_code = before_unconditional_jump(expected_code);
                actual_code = before_unconditional_jump(actual_code);
            }
            if let Some(copy) = monitor {
                (expected_code, actual_code) =
                    copy.source_code(instructions, pattern, sample, expected_code, actual_code)?;
            }
            if actual_code.len() < expected_code.len()
                || !actual_code
                    .iter()
                    .zip(expected_code)
                    .all(|(a, b)| {
                        same_instruction(a, b)
                            || (can_rename && local_renames.match_access(b, a))
                    })
            {
                return None;
            }
            if trim {
                continuation = Some(sample);
            } else {
                if expected_code.len() != actual_code.len()
                    || expected.successors.len() != actual.successors.len()
                {
                    return None;
                }
                removed.insert(sample_block);
                if let Some((edge, owner)) = departure
                    && edge.source == pattern
                {
                    // Both cleanup copies must unlock the very same dynamic
                    // monitor and transfer to the same external destination.
                    if owner.unlock_target(instructions, graph, sample) != Some(edge.target) {
                        return None;
                    }
                    continue;
                }
                pending.extend(
                    expected
                        .successors
                        .iter()
                        .copied()
                        .zip(actual.successors.iter().copied()),
                );
            }
        }
        if let Some(copy) = monitor {
            if copy.pattern.handler_blocks().count() != copy.sample.handler_blocks().count()
                || copy.pattern.handler.has_self_protected_prefix()
                    != copy.sample.handler.has_self_protected_prefix()
            {
                return None;
            }
            for (pattern, sample) in copy.pattern.handler_blocks().zip(copy.sample.handler_blocks())
            {
                let pattern_block = &graph.blocks[pattern];
                let sample_block = &graph.blocks[sample];
                if self.blocks.contains(&sample)
                    || body.contains(&sample)
                    || !copies.insert(sample)
                    || !removed.insert(sample)
                    || !same_dispatch(&routes[pattern], &routes[sample], monitor)
                    || pattern_block.exception_successors.contains(&copy.pattern.handler.start)
                        != sample_block.exception_successors.contains(&copy.sample.handler.start)
                {
                    return None;
                }
            }
            if copy.sample.handler_blocks().any(|block| {
                graph.blocks[block]
                    .exception_predecessors
                    .iter()
                    .any(|pred| !removed.contains(pred))
            }) {
                return None;
            }
        }
        for &pattern in self.nested_handlers.keys() {
            let &sample = paired.get(&pattern)?;
            if graph.blocks[sample].exception_predecessors.iter().any(|pred| !removed.contains(pred)) {
                return None;
            }
        }
        // A different slot can hold the corresponding nested exception
        // only when neither binding can be read, even after a CFG join.
        if !renamed.is_empty() && instructions.iter().any(|op| {
            renamed.iter().copied().any(|slot| cleanup_locals::reads(op, slot))
        }) {
            return None;
        }
        for &sample in &removed {
            if graph.blocks[sample].predecessors.iter().any(|pred| {
                !removed.contains(pred) && (sample != sample_start || !body.contains(pred))
            }) {
                return None;
            }
        }
        if !local_renames.is_empty() || sample_binding.is_some() {
            self.verify_local_copies(
                instructions, graph, handler, sample_start, sample_binding, &paired, &local_renames,
            )?;
        }
        let copied_exit = departure.and_then(|(edge, _)| paired.get(&edge.source).copied());
        if self.tail.is_some() != continuation.is_some() {
            return None;
        }
        Some((continuation, removed, copied_exit, copied_routes))
    }

    fn verify_local_copies(
        &self,
        instructions: &[Instruction],
        graph: &ControlFlowGraph,
        handler: usize,
        sample_entry: usize,
        sample_binding: Option<cleanup_locals::Local>,
        paired: &BTreeMap<usize, usize>,
        renames: &cleanup_locals::Renames,
    ) -> Option<()> {
        let mut pattern_ranges = BTreeMap::new();
        let mut sample_ranges = BTreeMap::new();
        for (&pattern, &sample) in paired {
            let expected = &graph.blocks[pattern].instructions;
            let actual = &graph.blocks[sample].instructions;
            let left = expected.start + usize::from(pattern == handler);
            let right = actual.start + usize::from(sample == sample_entry && sample_binding.is_some());
            let (a, b) = if Some(pattern) == self.tail {
                let end = self.tail_code.end;
                (left..end, right..right + end - left)
            } else {
                (left..expected.end, right..actual.end)
            };
            if instructions[a.clone()].iter().zip(&instructions[b.clone()])
                .any(|(pattern, sample)| !renames.keeps_bijection(pattern, sample))
            {
                return None;
            }
            pattern_ranges.insert(pattern, a);
            sample_ranges.insert(sample, b);
        }
        let private = |ranges, entry, local| {
            cleanup_locals::private_copy_local(instructions, graph, ranges, entry, local)
        };
        let dead = |ranges, local| cleanup_locals::dead_after_copy(instructions, graph, ranges, local);
        if sample_binding.is_some_and(|local| !private(&sample_ranges, sample_entry, local))
            || renames.pairs().any(|(a, b)| {
                !private(&pattern_ranges, self.entry, a) || !private(&sample_ranges, sample_entry, b)
                    // The retained copy runs on paths formerly owned by the
                    // sibling. Neither lane may affect their live-out state.
                    || !dead(&sample_ranges, a) || !dead(&pattern_ranges, b)
            })
        {
            return None;
        }
        Some(())
    }

    fn resume_overriding_void(
        &mut self,
        instructions: &[Instruction],
        graph: &ControlFlowGraph,
        routes: &[Vec<Route>],
        inner_handler: usize,
        continuing: BTreeMap<usize, Option<usize>>,
    ) -> Option<()> {
        if self.tail.is_none()
            || self.shared_return.is_some()
            || self.monitor_exit.is_some()
            || !self.loop_targets.is_empty()
            || !self.returns.is_empty()
            || continuing.len() != 2
        {
            return None;
        }
        let &[on_throw] = graph.blocks[inner_handler].successors.as_slice() else { return None; };
        continuing.get(&on_throw)?;
        for tail in continuing.values() {
            let tail = (*tail)?;
            let node = &graph.blocks[tail];
            let start = node.instructions.start + self.tail_code.len();
            if !matches!(&instructions[start..node.instructions.end], [Instruction { opcode: 0xb1, .. }])
                || !routes[tail].is_empty()
                || !node.exception_predecessors.is_empty()
                || node.predecessors.iter().any(|pred| !self.removed.contains(pred))
            {
                return None;
            }
            self.removed.insert(tail);
        }
        let (&entry, &tail) = continuing.iter().find(|&(&entry, _)| entry != on_throw)?;
        self.forced_return = Some(graph.blocks[tail?].instructions.end - 1);
        self.body_join = Some(entry);
        self.projected_entries = continuing.into_keys().collect();
        Some(())
    }
}

#[derive(Clone, Copy)]
struct MonitorCopy<'a> {
    pattern: &'a MonitorPlan,
    sample: &'a MonitorPlan,
}

impl MonitorCopy<'_> {
    fn source_code<'a>(
        self,
        instructions: &[Instruction],
        pattern: usize,
        sample: usize,
        mut expected: &'a [Instruction],
        mut actual: &'a [Instruction],
    ) -> Option<(&'a [Instruction], &'a [Instruction])> {
        if pattern == self.pattern.acquisition {
            if sample != self.sample.acquisition {
                return None;
            }
            expected = expected.get(..expected.len().checked_sub(self.pattern.scaffold.len())?)?;
            actual = actual.get(..actual.len().checked_sub(self.sample.scaffold.len())?)?;
        } else if sample == self.sample.acquisition {
            return None;
        }
        match (self.pattern.releases.get(&pattern), self.sample.releases.get(&sample)) {
            (Some(release), Some(copy))
                if expected.last()?.offset == instructions[release.end - 1].offset
                    && actual.last()?.offset == instructions[copy.end - 1].offset =>
            {
                // Only the confirmed synthetic releases may differ in their
                // local slot. The acquisition expressions and body stay exact.
                expected = &expected[..expected.len().checked_sub(release.len())?];
                actual = &actual[..actual.len().checked_sub(copy.len())?];
            }
            (None, None) => {}
            _ => return None,
        }
        Some((expected, actual))
    }
}

fn same_dispatch(pattern: &[Route], sample: &[Route], monitor: Option<MonitorCopy<'_>>) -> bool {
    pattern.len() == sample.len()
        && pattern.iter().zip(sample).all(|(pattern, sample)| {
            if let Some(copy) = monitor
                && pattern.handler == copy.pattern.handler.start
            {
                pattern.catch_type == 0
                    && sample.catch_type == 0
                    && sample.handler == copy.sample.handler.start
            } else {
                pattern == sample
            }
        })
}

fn before_unconditional_jump(code: &[Instruction]) -> &[Instruction] {
    match code {
        [body @ .., last] if matches!(last.opcode, 0xa7 | 0xc8) => body,
        _ => code,
    }
}

fn goto_only(instructions: &[Instruction], graph: &ControlFlowGraph, block: usize) -> Option<usize> {
    let node = &graph.blocks[block];
    let &[next] = node.successors.as_slice() else { return None; };
    matches!(&instructions[node.instructions.clone()], [Instruction { opcode: 0xa7 | 0xc8, .. }])
        .then_some(next)
}

fn private_forward_goto(
    instructions: &[Instruction],
    graph: &ControlFlowGraph,
    routes: &[Vec<Route>],
    block: usize,
) -> Option<usize> {
    let node = &graph.blocks[block];
    if node.predecessors.len() != 1
        || !node.exception_predecessors.is_empty()
        || !routes[block].is_empty()
    {
        return None;
    }
    goto_only(instructions, graph, block).filter(|&next| next > block)
}

fn explicit_jump(
    instructions: &[Instruction],
    graph: &ControlFlowGraph,
    source: usize,
    target: usize,
) -> Option<usize> {
    let node = &graph.blocks[source];
    let jump = node.instructions.end - 1;
    (node.successors == [target] && matches!(instructions[jump].opcode, 0xa7 | 0xc8))
        .then_some(jump)
}

fn same_instruction(sample: &Instruction, pattern: &Instruction) -> bool {
    if sample.opcode != pattern.opcode
        && !(matches!(sample.opcode, 0xa7 | 0xc8) && matches!(pattern.opcode, 0xa7 | 0xc8))
    {
        return false;
    }
    match (&sample.operand, &pattern.operand) {
        (Operand::Branch(_), Operand::Branch(_)) => true,
        (
            Operand::Switch {
                default: a,
                cases: left,
            },
            Operand::Switch {
                default: b,
                cases: right,
            },
        ) => {
            if left.len() != right.len() {
                return false;
            }
            // The CFG orders each target by its first occurrence. Check the
            // case labels and the same equivalence classes of destinations,
            // including labels sharing the default destination.
            let mut left_to_right = BTreeMap::from([(*a, *b)]);
            let mut right_to_left = BTreeMap::from([(*b, *a)]);
            left.iter()
                .zip(right)
                .all(|(&(left_key, left), &(right_key, right))| {
                    left_key == right_key
                        && *left_to_right.entry(left).or_insert(right) == right
                        && *right_to_left.entry(right).or_insert(left) == left
                })
        }
        (a, b) => a == b,
    }
}
