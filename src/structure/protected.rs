// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

pub(super) mod cleanup_locals;
mod finally_graph;
mod legacy_resource;
mod monitor;
mod overriding_finally;

use std::collections::{BTreeMap, BTreeSet};
use std::ops::Range;

use crate::bytecode::{Instruction, Operand};
use crate::cfg::ControlFlowGraph;
use crate::classfile::ExceptionHandler;
use crate::lift::Machine;

use self::finally_graph::BranchedFinally;
use self::legacy_resource::LegacyResource;
use self::monitor::{MonitorHandler, MonitorPlan};
use self::overriding_finally::OverridingReturn;
use super::StructureError;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct ArmId(usize);

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ExceptionId(usize);

#[derive(Default)]
pub(super) struct Exceptions {
    regions: Vec<ProtectedRegion>,
    arms: Vec<Arm>,
    entries: BTreeMap<(Option<ArmId>, usize), ExceptionId>,
    routes: Vec<Vec<Route>>,
    bindings: BTreeSet<usize>,
    return_splits: BTreeMap<usize, usize>,
    cleanup_prefixes: BTreeMap<usize, usize>,
    cleanup_copies: BTreeSet<usize>,
    terminal_cleanup_copies: BTreeSet<usize>,
    cleanup_returns: BTreeSet<usize>,
    cleanup_forward: BTreeSet<usize>,
    cleanup_bypasses: BTreeMap<usize, usize>,
    cleanup_landings: BTreeSet<usize>,
    monitor_acquisitions: BTreeMap<usize, usize>,
    omitted_instructions: BTreeSet<usize>,
}

pub(super) struct ProtectedRegion {
    pub(super) start: usize,
    pub(super) body: ArmId,
    pub(super) catches: Vec<Catch>,
    pub(super) finally: Option<Finally>,
    pub(super) monitor: Option<Monitor>,
    pub(super) legacy_resource: Option<Legacy>,
    pub(super) join: Option<usize>,
    pub(super) split_resource_exits: Vec<usize>,
    enclosing: Option<ArmId>,
}

pub(super) struct Catch {
    pub(super) arm: ArmId,
    pub(super) start: usize,
    pub(super) alternatives: Vec<u16>,
}

pub(super) struct Finally {
    pub(super) arm: ArmId,
    plan: Cleanup,
}

pub(super) struct Monitor {
    arm: ArmId,
    pub(super) plan: MonitorPlan,
}

pub(super) struct Legacy {
    pub(super) arm: ArmId,
    pub(super) acquisition: usize,
    pub(super) slot: u16,
    pub(super) exit: LegacyExit,
}

pub(super) enum LegacyExit {
    Continue(usize),
    Return {
        spill: usize,
        block: usize,
        transfer: usize,
    },
}

struct Cleanup {
    start: usize,
    block: usize,
    instructions: Range<usize>,
    branched: Option<BranchedFinally>,
    terminal_copies: Option<BTreeSet<usize>>,
    overriding_return: Option<OverridingReturn>,
    spill_offsets: Vec<(usize, usize)>,
}

enum CleanupPlan {
    Finally(Cleanup),
    Monitor(MonitorPlan),
}

impl Finally {
    pub(super) fn start(&self) -> usize {
        self.plan.start
    }

    pub(super) fn block(&self) -> usize {
        self.plan.block
    }

    pub(super) fn branched(&self) -> Option<&BranchedFinally> {
        self.plan.branched.as_ref()
    }

    pub(super) fn terminal_copies(&self) -> Option<&BTreeSet<usize>> {
        self.plan.terminal_copies.as_ref()
    }

    pub(super) fn overriding_return(&self) -> Option<&OverridingReturn> {
        self.plan.overriding_return.as_ref()
    }

    /// (return opcode, original spill store) instruction indices.
    pub(super) fn spill_offsets(&self) -> &[(usize, usize)] {
        &self.plan.spill_offsets
    }
}

struct Arm {
    region: ExceptionId,
    blocks: BTreeSet<usize>,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Route {
    handler: usize,
    catch_type: u16,
}

struct Table {
    by_block: Vec<Vec<Route>>,
    by_range: BTreeMap<Vec<usize>, Vec<Route>>,
    monitor_handlers: BTreeMap<usize, MonitorHandler>,
}

fn unsupported() -> StructureError {
    StructureError::ExceptionHandlers
}

impl Exceptions {
    pub(super) fn new(
        instructions: &[Instruction],
        graph: &ControlFlowGraph,
        handlers: &[ExceptionHandler],
        machine: Option<&Machine<'_, '_>>,
    ) -> Result<Self, StructureError> {
        if handlers.is_empty() {
            return Ok(Self::default());
        }
        let mut table = Table::new(instructions, graph, handlers)?;
        let dominators = Dominance::new(graph);
        let mut result = Self::default();
        if let Some(machine) = machine {
            result.classify_legacy_resources(instructions, graph, &mut table, machine)?;
        }
        let mut cleanups = BTreeMap::new();
        // Register verified normal copies before classifying bodies. A copy
        // can be an exit of both a finally and its nested typed catch.
        for (covered, routes) in &table.by_range {
            if let Some(route) = routes.iter().find(|route| route.catch_type == 0) {
                if Some(route) != routes.last() {
                    return Err(unsupported());
                }
                let body = covered.iter().copied().collect();
                let plan = if let Some(handler) = table.monitor_handlers.remove(&route.handler) {
                    if routes.len() != 1 {
                        return Err(unsupported());
                    }
                    let monitor = MonitorPlan::prove(instructions, graph, &body, handler)
                        .ok_or_else(unsupported)?;
                    if result
                        .monitor_acquisitions
                        .insert(monitor.acquisition, monitor.scaffold.start)
                        .is_some()
                    {
                        return Err(unsupported());
                    }
                    for release in monitor.releases.values() {
                        for instruction in release.clone() {
                            if !result.omitted_instructions.insert(instruction) {
                                return Err(unsupported());
                            }
                        }
                    }
                    CleanupPlan::Monitor(monitor)
                } else {
                    CleanupPlan::Finally(result.prepare_cleanup(
                        instructions,
                        graph,
                        &table,
                        &body,
                        route.handler,
                    )?)
                };
                if cleanups.insert(route.handler, plan).is_some() {
                    return Err(unsupported());
                }
            }
        }
        for (covered, routes) in &table.by_range {
            result.classify(
                instructions,
                graph,
                &dominators,
                &table,
                covered,
                routes,
                &mut cleanups,
                machine,
            )?;
        }
        let owners = result.link()?;
        result.verify_dispatch(&table, &owners)?;
        result.routes = table.by_block;
        Ok(result)
    }

    fn classify_legacy_resources(
        &mut self,
        instructions: &[Instruction],
        graph: &ControlFlowGraph,
        table: &mut Table,
        machine: &Machine<'_, '_>,
    ) -> Result<(), StructureError> {
        loop {
            let mut proven = None;
            for (covered, routes) in &table.by_range {
                for route in routes.iter().filter(|route| route.catch_type == 0) {
                    if let Some(plan) = LegacyResource::prove(
                        instructions,
                        graph,
                        &table.by_block,
                        machine,
                        covered,
                        route.handler,
                    )? {
                        proven = Some(plan);
                        break;
                    }
                }
                if proven.is_some() {
                    break;
                }
            }
            let Some(plan) = proven else { return Ok(()) };
            let mut rows = plan.copies.iter();
            let Some((&close, &next)) = rows.next() else {
                return Err(unsupported());
            };
            if rows.next().is_some() {
                // The regular structurer must own distinct departures
                // (including labeled break/continue) before we hide them.
                return Err(unsupported());
            }
            let scaffold = plan.scaffold;
            let id = ExceptionId(self.regions.len());
            let body = self.add_arm(id, plan.covered);
            let arm = self.add_arm(id, scaffold);
            let exit = if let Some(returned) = plan.returned {
                LegacyExit::Return {
                    spill: returned.spill,
                    block: returned.block,
                    transfer: returned.transfer,
                }
            } else {
                LegacyExit::Continue(next)
            };
            self.regions.push(ProtectedRegion {
                start: plan.start,
                body,
                catches: Vec::new(),
                finally: None,
                monitor: None,
                legacy_resource: Some(Legacy {
                    arm,
                    acquisition: plan.acquisition,
                    slot: plan.resource,
                    exit,
                }),
                join: Some(close),
                split_resource_exits: Vec::new(),
                enclosing: None,
            });
            self.omitted_instructions.extend(plan.null_init);
            for routes in &mut table.by_block {
                routes.retain(|route| !plan.routes.contains(route));
            }
            for routes in table.by_range.values_mut() {
                routes.retain(|route| !plan.routes.contains(route));
            }
            table.by_range.retain(|_, routes| !routes.is_empty());
        }
    }

    pub(super) fn at_start(&self, arm: Option<ArmId>, block: usize) -> Option<ExceptionId> {
        self.entries.get(&(arm, block)).copied()
    }

    pub(super) fn children_of(&self, arm: ArmId) -> impl Iterator<Item = ExceptionId> + '_ {
        self.entries
            .range((Some(arm), 0)..=(Some(arm), usize::MAX))
            .map(|(_, &id)| id)
    }

    pub(super) fn contains(&self, arm: Option<ArmId>, block: usize) -> bool {
        arm.is_none_or(|arm| self.arms[arm.0].blocks.contains(&block))
    }

    pub(super) fn arm_blocks(&self, arm: ArmId) -> impl Iterator<Item = usize> + '_ {
        self.arms[arm.0].blocks.iter().copied()
    }

    pub(super) fn matches_dispatch(
        &self,
        sample: usize,
        original: usize,
        ignored_handler: Option<usize>,
    ) -> bool {
        self.routes[sample]
            .iter()
            .filter(|route| Some(route.handler) != ignored_handler)
            .eq(&self.routes[original])
    }

    pub(super) fn region(&self, id: ExceptionId) -> &ProtectedRegion {
        &self.regions[id.0]
    }

    pub(super) fn catches_of_finally<'s>(
        &'s self,
        outer: &ProtectedRegion,
    ) -> Option<&'s ProtectedRegion> {
        if outer.finally.is_none() || !outer.catches.is_empty() {
            return None;
        }
        let inner = self.region(self.at_start(Some(outer.body), outer.start)?);
        if inner.finally.is_some()
            || inner.monitor.is_some()
            || inner.legacy_resource.is_some()
            || inner.join != outer.join
        {
            return None;
        }
        // The hierarchy already proves that the inner arms are disjoint
        // subsets. Equal sizes mean no additional statement in the body.
        let count = self.arms[inner.body.0].blocks.len()
            + inner
                .catches
                .iter()
                .map(|catch| self.arms[catch.arm.0].blocks.len())
                .sum::<usize>();
        (count == self.arms[outer.body.0].blocks.len()).then_some(inner)
    }

    pub(super) fn skips_binding(&self, block: usize) -> bool {
        self.bindings.contains(&block)
    }

    pub(super) fn return_split(&self, arm: Option<ArmId>, block: usize) -> Option<usize> {
        let split = *self.return_splits.get(&block)?;
        self.contains(arm, split).then_some(split)
    }

    pub(super) fn skips_instruction(&self, index: usize) -> bool {
        self.omitted_instructions.contains(&index)
    }

    pub(super) fn bypass_cleanup(&self, block: usize) -> usize {
        self.cleanup_bypasses.get(&block).copied().unwrap_or(block)
    }

    pub(super) fn monitor_acquisition_end(&self, block: usize) -> Option<usize> {
        self.monitor_acquisitions.get(&block).copied()
    }

    pub(super) fn cleanup_prefix(&self, block: usize) -> usize {
        self.cleanup_prefixes.get(&block).copied().unwrap_or(0)
    }

    pub(super) fn finally_range(&self, arm: Option<ArmId>, block: usize) -> Option<Range<usize>> {
        let arm = arm?;
        let finally = self.region(self.arms[arm.0].region).finally.as_ref()?;
        (finally.arm == arm && finally.plan.block == block)
            .then(|| finally.plan.instructions.clone())
    }

    fn add_arm(&mut self, region: ExceptionId, blocks: BTreeSet<usize>) -> ArmId {
        let id = ArmId(self.arms.len());
        self.arms.push(Arm { region, blocks });
        id
    }

    fn classify(
        &mut self,
        instructions: &[Instruction],
        graph: &ControlFlowGraph,
        dominators: &Dominance,
        table: &Table,
        covered: &[usize],
        routes: &[Route],
        cleanups: &mut BTreeMap<usize, CleanupPlan>,
        machine: Option<&Machine<'_, '_>>,
    ) -> Result<(), StructureError> {
        let id = ExceptionId(self.regions.len());
        let mut body: BTreeSet<_> = covered.iter().copied().collect();
        let finally_route = routes.iter().find(|route| route.catch_type == 0);
        if routes.iter().any(|route| {
            route.handler == 0
                || body.contains(&route.handler)
                || !graph.blocks[route.handler].predecessors.is_empty()
        }) {
            return Err(unsupported());
        }
        let mut finally = None;
        let mut monitor = None;
        if let Some(route) = finally_route {
            match cleanups.remove(&route.handler).ok_or_else(unsupported)? {
                CleanupPlan::Finally(mut plan) => {
                    let blocks = if let Some(branch) = &mut plan.branched {
                        if branch.entry == plan.start {
                            self.bindings.insert(plan.start);
                        }
                        std::mem::take(&mut branch.blocks)
                    } else {
                        BTreeSet::from([plan.start, plan.block])
                    };
                    let arm = self.add_arm(id, blocks);
                    finally = Some(Finally { arm, plan });
                }
                CleanupPlan::Monitor(plan) => {
                    body.extend(plan.releases.keys().copied());
                    let arm = self.add_arm(id, plan.handler_blocks().collect());
                    monitor = Some(Monitor { arm, plan });
                }
            }
        }
        let mut pending: BTreeSet<_> = normal_exits(graph, &body).collect();
        let mut exits = BTreeSet::new();
        // A protected range can end immediately before an exclusive goto or
        // return. These instructions themselves cannot throw. Preserve their
        // source placement, particularly returns whose value is still stacked.
        while let Some(exit) = pending.pop_first() {
            let exit = self.bypass_cleanup(exit);
            if body.contains(&exit) {
                continue;
            }
            if self.can_include_exit(instructions, graph, table, &body, exit) {
                exits.remove(&exit);
                body.insert(exit);
                pending.extend(graph.blocks[exit].successors.iter().copied());
            } else {
                exits.insert(exit);
            }
        }
        let start = single_entry(graph, &body)?;
        let mut catches: Vec<Catch> = Vec::new();
        let mut handlers = BTreeSet::new();
        for &route in routes.iter().filter(|route| route.catch_type != 0) {
            if let Some(catch) = catches
                .last_mut()
                .filter(|catch| catch.start == route.handler)
            {
                catch.alternatives.push(route.catch_type);
                continue;
            }
            if !handlers.insert(route.handler)
                || reference_store(&instructions[graph.blocks[route.handler].instructions.start])
                    .is_none()
            {
                return Err(unsupported());
            }
            let blocks = catch_blocks(graph, dominators, &body, route.handler, self)?;
            exits.extend(
                normal_exits(graph, &blocks)
                    .map(|next| self.bypass_cleanup(next))
                    .filter(|next| !blocks.contains(next)),
            );
            let arm = self.add_arm(id, blocks);
            self.bindings.insert(route.handler);
            catches.push(Catch {
                arm,
                start: route.handler,
                alternatives: vec![route.catch_type],
            });
        }
        if exits.len() > 1 {
            // An ordinary try has one normal continuation. Leave separate
            // edges intact only for a possible resource with inlined closes;
            // its emitter must prove those exits before consuming any copy.
            let (Some(machine), [route]) = (machine, routes) else {
                return Err(unsupported());
            };
            if route.catch_type == 0
                || machine.exception_class(route.catch_type)? != "java/lang/Throwable"
            {
                return Err(unsupported());
            }
        }
        if let Some(branch) = finally.as_ref().and_then(Finally::branched)
            && exits.first().copied() != branch.body_join
        {
            return Err(unsupported());
        }
        let body = self.add_arm(id, body);
        self.regions.push(ProtectedRegion {
            start,
            body,
            catches,
            finally,
            monitor,
            legacy_resource: None,
            join: exits.pop_first(),
            split_resource_exits: exits.into_iter().collect(),
            enclosing: None,
        });
        Ok(())
    }

    pub(super) fn enclosing_terminal_copy(
        &self,
        arm: Option<ArmId>,
        block: usize,
    ) -> Option<usize> {
        let arm = arm?;
        let region = self.region(self.arms[arm.0].region);
        let finally = region.finally.as_ref()?;
        let copies = finally.terminal_copies()?;
        let canonical = self.bypass_cleanup(block);
        (region.body == arm
            && region.join == Some(canonical)
            && copies.contains(&block))
        .then_some(canonical)
    }

    fn is_cleanup_copy(&self, block: usize) -> bool {
        self.cleanup_copies.contains(&block) || self.terminal_cleanup_copies.contains(&block)
    }

    fn can_include_exit(
        &mut self,
        instructions: &[Instruction],
        graph: &ControlFlowGraph,
        table: &Table,
        body: &BTreeSet<usize>,
        exit: usize,
    ) -> bool {
        let block = &graph.blocks[exit];
        if exit == 0
            || self.is_cleanup_copy(exit)
            || !block.exception_predecessors.is_empty()
            || block.predecessors.iter().any(|pred| !body.contains(pred))
            || table.by_block[exit].iter().any(|route| {
                !block
                    .predecessors
                    .iter()
                    .any(|&pred| table.by_block[pred].contains(route))
            })
        {
            return false;
        }
        if self.cleanup_returns.contains(&exit) {
            return true;
        }
        let prefix = self.cleanup_prefix(exit);
        let start = block.instructions.start + prefix;
        let mut remaining =
            (start..block.instructions.end).filter(|&index| !self.skips_instruction(index));
        let Some(next) = remaining.next() else {
            return block.successors.len() == 1;
        };
        if remaining.next().is_some() {
            return false;
        }
        match instructions[next].opcode {
            0xa7 | 0xc8 => true,
            0xac..=0xb1 if next != start => true,
            0xac..=0xb1 if prefix == 0 => {
                if let [pred] = block.predecessors.as_slice() {
                    let predecessor = &graph.blocks[*pred];
                    if predecessor.instructions.end == start
                        && predecessor.successors == [exit]
                        && !matches!(
                            instructions[predecessor.instructions.end - 1].opcode,
                            0x99..=0xab | 0xc6..=0xc9
                        )
                    {
                        self.return_splits.insert(*pred, exit);
                        return true;
                    }
                }
                false
            }
            _ => false,
        }
    }

    fn prepare_cleanup(
        &mut self,
        instructions: &[Instruction],
        graph: &ControlFlowGraph,
        table: &Table,
        body: &BTreeSet<usize>,
        handler: usize,
    ) -> Result<Cleanup, StructureError> {
        let node = &graph.blocks[handler];
        let head = if node.instructions.len() == 1 {
            *node.successors.first().ok_or_else(unsupported)?
        } else {
            handler
        };
        if graph.blocks[head].successors.is_empty() {
            return self.prepare_finally(instructions, graph, table, body, handler);
        }
        if let Some(plan) =
            self.prove_overriding_resource_finally(instructions, graph, table, body, handler)
        {
            return Ok(plan);
        }
        let mut branch =
            BranchedFinally::prove(instructions, graph, &table.by_block, body, handler)
                .ok_or_else(unsupported)?;
        for &copy in &branch.removed {
            if self.cleanup_prefixes.contains_key(&copy)
                || self.cleanup_landings.contains(&copy)
                || self.terminal_cleanup_copies.contains(&copy)
                || !self.cleanup_copies.insert(copy)
            {
                return Err(unsupported());
            }
        }
        if !branch.projected_entries.is_empty() {
            let next = branch.continuation.ok_or_else(unsupported)?;
            if self.is_cleanup_copy(next) {
                return Err(unsupported());
            }
            self.cleanup_landings.insert(next);
            for entry in std::mem::take(&mut branch.projected_entries) {
                if self.cleanup_bypasses.insert(entry, next).is_some() {
                    return Err(unsupported());
                }
            }
        }
        let instructions = std::mem::take(&mut branch.tail_code);
        if let Some(next) = branch.prefix_block
            && !instructions.is_empty()
            && (self.is_cleanup_copy(next)
                || self
                    .cleanup_prefixes
                    .insert(next, instructions.len())
                    .is_some())
        {
            return Err(unsupported());
        }
        Ok(Cleanup {
            start: handler,
            block: branch.tail,
            instructions,
            branched: Some(branch),
            terminal_copies: None,
            overriding_return: None,
            spill_offsets: Vec::new(),
        })
    }

    fn prepare_finally(
        &mut self,
        instructions: &[Instruction],
        graph: &ControlFlowGraph,
        table: &Table,
        body: &BTreeSet<usize>,
        handler: usize,
    ) -> Result<Cleanup, StructureError> {
        if handler == 0 || body.contains(&handler) || !graph.blocks[handler].predecessors.is_empty()
        {
            return Err(unsupported());
        }
        let entry = &graph.blocks[handler];
        let throwable =
            reference_store(&instructions[entry.instructions.start]).ok_or_else(unsupported)?;
        // Some compilers emit a separate self-protected astore block. It is
        // not part of the cleanup; the matched copy starts at its successor.
        let (block, start) = if entry.instructions.len() == 1 {
            let &[next] = entry.successors.as_slice() else {
                return Err(unsupported());
            };
            if graph.blocks[next].predecessors != [handler] {
                return Err(unsupported());
            }
            (next, graph.blocks[next].instructions.start)
        } else {
            (handler, entry.instructions.start + 1)
        };
        let cleanup = &graph.blocks[block];
        let full_end = cleanup.instructions.end;
        let rethrow = full_end.checked_sub(2).filter(|&load| {
            load >= start
                && reference_load(&instructions[load]) == Some(throwable)
                && instructions[load + 1].opcode == 0xbf
        });
        if rethrow.is_none() && !matches!(instructions[full_end - 1].opcode, 0xac..=0xb1 | 0xbf) {
            return Err(unsupported());
        }
        let end = rethrow.unwrap_or(full_end);
        if body.contains(&block)
            || !cleanup.successors.is_empty()
            || instructions[start..end]
                .iter()
                .any(|instruction| local_touches(instruction, throwable))
            || body.iter().any(|&member| {
                matches!(
                    instructions[graph.blocks[member].instructions.end - 1].opcode,
                    0xac..=0xb1
                )
            })
        {
            return Err(unsupported());
        }
        let count = end - start;
        let exits: BTreeSet<_> = normal_exits(graph, body).collect();
        let terminal = rethrow.is_none();
        let canonical = exits.first().copied();
        let has_distinct_exits = exits.len() > 1;
        let mut spill_offsets = Vec::new();
        for &exit in &exits {
            let target = &graph.blocks[exit];
            if target.instructions.len() < count
                || self.is_cleanup_copy(exit)
                || (terminal && target.instructions.len() != count)
                || target.predecessors.iter().any(|pred| !body.contains(pred))
                || !target.exception_predecessors.is_empty()
                || table.by_block[exit] != table.by_block[block]
                || !cleanup_locals::same_cleanup(
                    instructions,
                    &instructions[start..end],
                    &instructions[target.instructions.start..target.instructions.start + count],
                )
            {
                return Err(unsupported());
            }
            if terminal {
                if self.cleanup_prefixes.contains_key(&exit)
                    || self.cleanup_landings.contains(&exit)
                    || !self.terminal_cleanup_copies.insert(exit)
                {
                    return Err(unsupported());
                }
                if let Some(next) = canonical
                    && exit != next
                    && self.cleanup_bypasses.insert(exit, next).is_some()
                {
                    return Err(unsupported());
                }
                continue;
            }
            // One physical copy cannot stand for cleanups of two distinct
            // exception regions: nesting would execute it twice.
            if count != 0 && self.cleanup_prefixes.insert(exit, count).is_some() {
                return Err(unsupported());
            }
            let suffix = target.instructions.start + count;
            match &instructions[suffix..target.instructions.end] {
                [load, transfer] => {
                    let Some(slot) = cleanup_locals::returned(load, transfer) else {
                        continue;
                    };
                    if instructions[start..end].iter().any(|op| slot.touches(op))
                        || instructions[target.instructions.start..suffix]
                            .iter()
                            .any(|op| slot.touches(op))
                    {
                        continue;
                    }
                    self.cleanup_returns.insert(exit);
                    // A dedicated spill/reload has no source-level lifetime.
                    // Its only observer is the return, provided an exception
                    // thrown by the copied cleanup cannot reach another arm.
                    if table.by_block[exit].is_empty()
                        && let [pred] = target.predecessors.as_slice()
                        && graph.blocks[*pred].successors == [exit]
                        && graph.blocks[*pred].instructions.end == target.instructions.start
                        && let store = graph.blocks[*pred].instructions.end - 1
                        && cleanup_locals::store(&instructions[store]) == Some(slot)
                    {
                        if !self.omitted_instructions.insert(store)
                            || !self.omitted_instructions.insert(suffix)
                        {
                            return Err(unsupported());
                        }
                        spill_offsets.push((suffix + 1, store));
                    }
                }
                [Instruction { opcode: 0xb1, .. }] if has_distinct_exits => {
                    // The copy ends in a void return, so there is no value
                    // spill to retain and no second normal continuation.
                    self.cleanup_returns.insert(exit);
                }
                []
                | [
                    Instruction {
                        opcode: 0xa7 | 0xc8,
                        ..
                    },
                ] if target.successors.len() == 1 => {
                    self.cleanup_forward.insert(exit);
                }
                _ => {}
            }
        }
        Ok(Cleanup {
            start: handler,
            block,
            instructions: start..end,
            branched: None,
            terminal_copies: terminal.then_some(exits),
            overriding_return: None,
            spill_offsets,
        })
    }

    fn link(&mut self) -> Result<BTreeMap<usize, ArmId>, StructureError> {
        let mut memberships: BTreeMap<usize, Vec<ArmId>> = BTreeMap::new();
        for (index, arm) in self.arms.iter().enumerate() {
            for &block in &arm.blocks {
                memberships.entry(block).or_default().push(ArmId(index));
            }
        }
        for (index, region) in self.regions.iter_mut().enumerate() {
            let arms = std::iter::once(region.body)
                .chain(region.catches.iter().map(|catch| catch.arm))
                .chain(region.finally.iter().map(|finally| finally.arm))
                .chain(region.monitor.iter().map(|monitor| monitor.arm))
                .chain(region.legacy_resource.iter().map(|resource| resource.arm));
            let mut enclosing = None;
            for &candidate in &memberships[&region.start] {
                let candidate_arm = &self.arms[candidate.0];
                if candidate_arm.region == ExceptionId(index) {
                    continue;
                }
                if arms
                    .clone()
                    .all(|arm| self.arms[arm.0].blocks.is_subset(&candidate_arm.blocks))
                    && region
                        .legacy_resource
                        .as_ref()
                        .is_none_or(|resource| candidate_arm.blocks.contains(&resource.acquisition))
                    && region.monitor.as_ref().is_none_or(|monitor| {
                        candidate_arm.blocks.contains(&monitor.plan.acquisition)
                    })
                    && enclosing.is_none_or(|current: ArmId| {
                        candidate_arm.blocks.len() < self.arms[current.0].blocks.len()
                    })
                {
                    enclosing = Some(candidate);
                }
            }
            region.enclosing = enclosing;
            if self
                .entries
                .insert((enclosing, region.start), ExceptionId(index))
                .is_some()
            {
                return Err(unsupported());
            }
        }
        memberships
            .into_iter()
            .map(|(block, mut arms)| {
                arms.sort_unstable_by_key(|arm| self.arms[arm.0].blocks.len());
                // Every shared block must belong to a single ancestor chain.
                // Crossing protected ranges and reused handlers outside that
                // chain have no source-level nesting with these catch regions.
                for pair in arms.windows(2) {
                    let region = &self.regions[self.arms[pair[0].0].region.0];
                    if region.enclosing != Some(pair[1]) {
                        return Err(unsupported());
                    }
                }
                Ok((block, arms[0]))
            })
            .collect()
    }

    fn verify_dispatch(
        &self,
        table: &Table,
        owners: &BTreeMap<usize, ArmId>,
    ) -> Result<(), StructureError> {
        // Compare the order implied by lexical nesting with the actual
        // ordered exception table. In particular, set containment alone is
        // insufficient when the outer entries precede the inner entries.
        for (block, actual) in table.by_block.iter().enumerate() {
            let mut remaining = actual.iter();
            let mut owner = owners.get(&block).copied();
            while let Some(id) = owner {
                let region = &self.regions[self.arms[id.0].region.0];
                if region.body == id {
                    for expected in region
                        .catches
                        .iter()
                        .flat_map(|catch| {
                            catch.alternatives.iter().map(|&catch_type| Route {
                                handler: catch.start,
                                catch_type,
                            })
                        })
                        .chain(region.finally.iter().map(|finally| Route {
                            handler: finally.start(),
                            catch_type: 0,
                        }))
                        .chain(region.monitor.iter().map(|monitor| Route {
                            handler: monitor.plan.handler.start,
                            catch_type: 0,
                        }))
                    {
                        if remaining.as_slice().contains(&expected)
                            && remaining.next() != Some(&expected)
                        {
                            return Err(unsupported());
                        }
                    }
                }
                owner = region.enclosing;
            }
            if !remaining.as_slice().is_empty() {
                return Err(unsupported());
            }
        }
        Ok(())
    }
}

impl Table {
    fn new(
        instructions: &[Instruction],
        graph: &ControlFlowGraph,
        handlers: &[ExceptionHandler],
    ) -> Result<Self, StructureError> {
        let code_end = instructions.last().map(|last| last.offset + last.len);
        let mut by_block = vec![Vec::new(); graph.blocks.len()];
        let mut aggregate: BTreeMap<Route, usize> = BTreeMap::new();
        let mut ranges: Vec<(Route, Vec<usize>)> = Vec::new();
        let mut monitor_handlers = BTreeMap::new();
        for entry in handlers {
            let start = graph
                .block_at(entry.start_pc.into())
                .ok_or_else(unsupported)?;
            let end = if Some(entry.end_pc.into()) == code_end {
                graph.blocks.len()
            } else {
                graph
                    .block_at(entry.end_pc.into())
                    .ok_or_else(unsupported)?
            };
            let handler = graph
                .block_at(entry.handler_pc.into())
                .ok_or_else(unsupported)?;
            if entry.catch_type == 0
                && let std::collections::btree_map::Entry::Vacant(candidate) =
                    monitor_handlers.entry(handler)
                && let Some(monitor) = MonitorHandler::detect(instructions, graph, handler)
            {
                candidate.insert(monitor);
            }
            if start >= end {
                return Err(unsupported());
            }
            // An isolated store of the incoming throwable cannot transfer
            // to its own handler, even when a wider row covers the store.
            let own_exception_store = entry.catch_type == 0
                && graph.blocks[handler].instructions.len() == 1
                && reference_store(&instructions[graph.blocks[handler].instructions.start]).is_some();
            if own_exception_store && start == handler && end == handler + 1 {
                continue;
            }
            let route = Route {
                handler,
                catch_type: entry.catch_type,
            };
            let index = *aggregate.entry(route).or_insert_with(|| {
                let index = ranges.len();
                ranges.push((route, Vec::new()));
                index
            });
            for block in start..end {
                if entry.catch_type == 0
                    && block == handler
                    && (own_exception_store
                        || monitor_handlers
                            .get(&handler)
                            .is_some_and(MonitorHandler::has_self_protected_prefix))
                {
                    continue;
                }
                if !by_block[block].contains(&route) {
                    by_block[block].push(route);
                    ranges[index].1.push(block);
                }
            }
        }
        let mut by_range: BTreeMap<Vec<usize>, Vec<Route>> = BTreeMap::new();
        for (route, mut covered) in ranges {
            if covered.is_empty() {
                continue;
            }
            covered.sort_unstable();
            by_range.entry(covered).or_default().push(route);
        }
        if by_range.is_empty() {
            return Err(unsupported());
        }
        Ok(Self {
            by_block,
            by_range,
            monitor_handlers,
        })
    }
}

fn single_entry(graph: &ControlFlowGraph, body: &BTreeSet<usize>) -> Result<usize, StructureError> {
    let mut entries = body.iter().copied().filter(|&block| {
        let node = &graph.blocks[block];
        block == 0
            || node
                .predecessors
                .iter()
                .chain(&node.exception_predecessors)
                .any(|pred| !body.contains(pred))
    });
    let start = entries.next().ok_or_else(unsupported)?;
    if entries.next().is_some() {
        return Err(unsupported());
    }
    Ok(start)
}

fn normal_exits<'a>(
    graph: &'a ControlFlowGraph,
    blocks: &'a BTreeSet<usize>,
) -> impl Iterator<Item = usize> + 'a {
    blocks
        .iter()
        .flat_map(|&block| graph.blocks[block].successors.iter().copied())
        .filter(|next| !blocks.contains(next))
}

fn catch_blocks(
    graph: &ControlFlowGraph,
    dominance: &Dominance,
    body: &BTreeSet<usize>,
    handler: usize,
    exceptions: &Exceptions,
) -> Result<BTreeSet<usize>, StructureError> {
    let mut blocks = BTreeSet::new();
    let mut pending = vec![handler];
    while let Some(block) = pending.pop() {
        if !dominance.contains(handler, block) || !blocks.insert(block) {
            continue;
        }
        if body.contains(&block) {
            return Err(unsupported());
        }
        let node = &graph.blocks[block];
        // A matched finally copy identifies the end of the handler even
        // when that handler is the only arm that can complete normally.
        if !exceptions.cleanup_forward.contains(&block) {
            pending.extend(
                node.successors
                    .iter()
                    .copied()
                    .filter(|next| {
                        !exceptions.cleanup_bypasses.contains_key(next)
                            && !exceptions.terminal_cleanup_copies.contains(next)
                    }),
            );
        }
        pending.extend(node.exception_successors.iter().copied());
    }
    if blocks.is_empty() {
        return Err(unsupported());
    }
    Ok(blocks)
}

struct Dominance {
    spans: Vec<Range<usize>>,
}

impl Dominance {
    fn new(graph: &ControlFlowGraph) -> Self {
        let mut children = vec![Vec::new(); graph.blocks.len()];
        for (node, parent) in graph.immediate_dominators().into_iter().enumerate() {
            if let Some(parent) = parent {
                children[parent].push(node);
            }
        }
        let mut spans = vec![0..0; children.len()];
        let mut next = 1;
        let mut stack = vec![(0, children[0].iter())];
        while let Some((node, siblings)) = stack.last_mut() {
            if let Some(&child) = siblings.next() {
                spans[child].start = next;
                next += 1;
                stack.push((child, children[child].iter()));
            } else {
                spans[*node].end = next;
                stack.pop();
            }
        }
        Self { spans }
    }

    fn contains(&self, dominator: usize, node: usize) -> bool {
        self.spans[dominator].contains(&self.spans[node].start)
    }
}

pub(super) fn reference_store(instruction: &Instruction) -> Option<u16> {
    matches!(instruction.opcode, 0x3a | 0x4b..=0x4e)
        .then(|| local_access(instruction))
        .flatten()
}

pub(super) fn reference_load(instruction: &Instruction) -> Option<u16> {
    matches!(instruction.opcode, 0x19 | 0x2a..=0x2d)
        .then(|| local_access(instruction))
        .flatten()
}

fn local_access(instruction: &Instruction) -> Option<u16> {
    match (&instruction.operand, instruction.opcode) {
        (Operand::Local(slot) | Operand::Increment { index: slot, .. }, _) => Some(*slot),
        (_, opcode @ 0x1a..=0x2d) => Some(u16::from((opcode - 0x1a) % 4)),
        (_, opcode @ 0x3b..=0x4e) => Some(u16::from((opcode - 0x3b) % 4)),
        _ => None,
    }
}

pub(super) fn local_touches(instruction: &Instruction, slot: u16) -> bool {
    local_access(instruction).is_some_and(|index| {
        index == slot || index.checked_add(1) == Some(slot) && matches!(
            instruction.opcode,
            0x16 | 0x18 | 0x1e..=0x21 | 0x26..=0x29 | 0x37 | 0x39 | 0x3f..=0x42 | 0x47..=0x4a
        )
    })
}
