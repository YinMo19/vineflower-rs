// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use std::collections::{BTreeMap, BTreeSet};

use crate::bytecode::{Instruction, Operand};
use crate::cfg::ControlFlowGraph;
use crate::lift::{LiftError, Machine};

use super::{Route, cleanup_locals, local_touches, normal_exits, reference_load, reference_store};

pub(super) struct LegacyResource {
    pub(super) start: usize,
    pub(super) covered: BTreeSet<usize>,
    pub(super) acquisition: usize,
    pub(super) resource: u16,
    pub(super) null_init: [usize; 2],
    pub(super) returned: Option<Return>,
    pub(super) copies: BTreeMap<usize, usize>,
    pub(super) scaffold: BTreeSet<usize>,
    pub(super) routes: BTreeSet<Route>,
}

pub(super) struct Return {
    pub(super) spill: usize,
    pub(super) block: usize,
    pub(super) transfer: usize,
}

struct Proof<'a, 'm, 'class, 'context> {
    instructions: &'a [Instruction],
    graph: &'a ControlFlowGraph,
    routes: &'a [Vec<Route>],
    machine: &'m Machine<'class, 'context>,
}

struct Match {
    resource: u16,
    primary: u16,
    close: (u8, u16),
    continuation: usize,
    removed: BTreeSet<usize>,
    suppression: Route,
    suppressed: u16,
}

impl LegacyResource {
    /// Match javac 7/8's primary-exception local and duplicated cleanup.
    /// The normal diamond is kept in the proof even though its suppression
    /// arm is unreachable on a successful body path with the primary null.
    pub(super) fn prove(
        instructions: &[Instruction],
        graph: &ControlFlowGraph,
        routes: &[Vec<Route>],
        machine: &Machine<'_, '_>,
        guarded: &[usize],
        close_handler: usize,
    ) -> Result<Option<Self>, LiftError> {
        let proof = Proof {
            instructions,
            graph,
            routes,
            machine,
        };
        proof.prove(guarded, close_handler)
    }
}

impl Proof<'_, '_, '_, '_> {
    fn prove(
        &self,
        guarded: &[usize],
        close_handler: usize,
    ) -> Result<Option<LegacyResource>, LiftError> {
        let mut guarded: BTreeSet<_> = guarded.iter().copied().collect();
        if close_handler == 0 || !self.graph.blocks[close_handler].predecessors.is_empty() {
            return Ok(None);
        }
        let Some(final_entry) = self.block(close_handler).first().and_then(reference_store) else {
            return Ok(None);
        };
        let Some(final_check) = self.after_prefix(close_handler, 1) else {
            return Ok(None);
        };
        let Some(exceptional) = self.diamond(final_check)? else {
            return Ok(None);
        };
        let resource = exceptional.resource;
        let primary = exceptional.primary;
        if resource == primary
            || resource == final_entry
            || primary == final_entry
            || exceptional.suppressed == final_entry
        {
            return Ok(None);
        }
        let [load, throw] = self.block(exceptional.continuation) else {
            return Ok(None);
        };
        let rethrow = &self.graph.blocks[exceptional.continuation];
        if reference_load(load) != Some(final_entry)
            || throw.opcode != 0xbf
            || !rethrow.exception_predecessors.is_empty()
            || rethrow
                .predecessors
                .iter()
                .any(|pred| !exceptional.removed.contains(pred))
        {
            return Ok(None);
        }
        // The final catch-all row may include its own first astore. It is
        // nonthrowing and the observed graph proves that no self-rethrow
        // is hidden here.
        guarded.remove(&close_handler);
        let mut candidates = guarded.iter().copied().filter(|&block| {
            let [store, copy, save, reload, throw] = self.block(block) else {
                return false;
            };
            let Some(caught) = reference_store(store) else {
                return false;
            };
            caught != resource
                && caught != primary
                && reference_load(copy) == Some(caught)
                && reference_store(save) == Some(primary)
                && reference_load(reload) == Some(caught)
                && throw.opcode == 0xbf
                && self.graph.blocks[block].predecessors.is_empty()
        });
        let Some(body_handler) = candidates.next() else {
            return Ok(None);
        };
        if candidates.next().is_some() {
            return Ok(None);
        }
        guarded.remove(&body_handler);
        if guarded.is_empty() {
            return Ok(None);
        }
        let catch_all = Route {
            handler: close_handler,
            catch_type: 0,
        };
        let [record, first_final, ..] = self.routes[*guarded.first().unwrap()].as_slice() else {
            return Ok(None);
        };
        if record.handler != body_handler || *first_final != catch_all {
            return Ok(None);
        }
        let record = *record;
        if !self.throwable(record)? || self.routes[body_handler].first() != Some(&catch_all) {
            return Ok(None);
        }
        for (block, routes) in self.routes.iter().enumerate() {
            if routes.contains(&record) != guarded.contains(&block)
                || (guarded.contains(&block) && !routes.starts_with(&[record, catch_all]))
                || (routes.contains(&catch_all)
                    && !guarded.contains(&block)
                    && block != body_handler
                    && block != close_handler)
            {
                return Ok(None);
            }
        }
        let exits: BTreeSet<_> = normal_exits(self.graph, &guarded).collect();
        if exits.is_empty()
            || guarded.iter().any(|&block| {
                self.block(block).iter().any(|op| {
                    local_touches(op, primary)
                        || (matches!(op.opcode, 0x36..=0x4e | 0x84) && local_touches(op, resource))
                        || matches!(op.opcode, 0xac..=0xb1)
                })
            })
        {
            return Ok(None);
        }
        let mut heads = guarded.iter().copied().filter(|&block| {
            self.graph.blocks[block]
                .predecessors
                .iter()
                .any(|pred| !guarded.contains(pred))
        });
        let Some(start) = heads.next() else {
            return Ok(None);
        };
        if heads.next().is_some() || start == 0 {
            return Ok(None);
        }
        let normal_preds = &self.graph.blocks[start].predecessors;
        let mut predecessors = normal_preds
            .iter()
            .copied()
            .filter(|pred| !guarded.contains(pred));
        let Some(acquisition) = predecessors.next() else {
            return Ok(None);
        };
        if predecessors.next().is_some() || self.graph.blocks[acquisition].successors != [start] {
            return Ok(None);
        }
        let [.., store, null, set_primary] = self.block(acquisition) else {
            return Ok(None);
        };
        if reference_store(store) != Some(resource)
            || null.opcode != 0x01
            || reference_store(set_primary) != Some(primary)
            || !self.graph.blocks[acquisition]
                .exception_predecessors
                .is_empty()
        {
            return Ok(None);
        }
        let init_end = self.graph.blocks[acquisition].instructions.end;
        let ambient = self.routes[exceptional.continuation].as_slice();
        let mut scaffold = BTreeSet::from([body_handler, close_handler, exceptional.continuation]);
        if !self.closed_side(
            &exceptional,
            final_check,
            Some(close_handler),
            &BTreeSet::new(),
            ambient,
        ) {
            return Ok(None);
        }
        scaffold.extend(exceptional.removed);
        let mut consumed_routes = BTreeSet::from([record, catch_all, exceptional.suppression]);
        let mut copies = BTreeMap::new();
        for exit in exits {
            let Some(normal) = self.diamond(exit)? else {
                return Ok(None);
            };
            if normal.resource != resource
                || normal.primary != primary
                || normal.close != exceptional.close
                || !self.closed_side(&normal, exit, None, &guarded, ambient)
                || normal.removed.iter().any(|block| !scaffold.insert(*block))
                || !consumed_routes.insert(normal.suppression)
            {
                return Ok(None);
            }
            copies.insert(exit, normal.continuation);
        }
        if scaffold
            .iter()
            .any(|block| guarded.contains(block) || *block == acquisition)
            || copies
                .values()
                .any(|target| scaffold.contains(target) || guarded.contains(target))
        {
            return Ok(None);
        }
        if ambient.iter().any(|route| {
            self.live_after(route.handler, primary) || self.live_after(route.handler, resource)
        }) {
            return Ok(None);
        }
        // Neither synthetic local may be observed after a normal close;
        // compiler slot reuse is permitted only after a definite overwrite.
        for &exit in copies.values() {
            if self.live_after(exit, primary) || self.live_after(exit, resource) {
                return Ok(None);
            }
        }
        // Preserve the complete ordered dispatch suffix for actual user
        // instructions. Both catch-all and primary bookkeeping must precede
        // all ambient handlers, and the latter must see cleanup failures.
        if guarded
            .iter()
            .any(|&block| &self.routes[block][2..] != ambient)
            || self.routes[body_handler].get(1..) != Some(ambient)
            || self.routes[close_handler]
                .iter()
                .copied()
                .filter(|&route| route != catch_all)
                .ne(ambient.iter().copied())
        {
            return Ok(None);
        }
        let returned = (copies.len() == 1)
            .then(|| copies.first_key_value())
            .flatten()
            .and_then(|(&close, &next)| {
                self.return_exit(&guarded, &scaffold, ambient, close, next, resource, primary)
            });
        Ok(Some(LegacyResource {
            start,
            covered: guarded,
            acquisition,
            resource,
            null_init: [init_end - 2, init_end - 1],
            returned,
            copies,
            scaffold,
            routes: consumed_routes,
        }))
    }

    fn return_exit(
        &self,
        body: &BTreeSet<usize>,
        scaffold: &BTreeSet<usize>,
        ambient: &[Route],
        close: usize,
        next: usize,
        resource: u16,
        primary: u16,
    ) -> Option<Return> {
        let target = &self.graph.blocks[next];
        let [load, transfer] = self.block(next) else {
            return None;
        };
        let local = cleanup_locals::returned(load, transfer)?;
        let &[spill] = self.graph.blocks[close].predecessors.as_slice() else {
            return None;
        };
        let store = self.block(spill).last()?;
        if !body.contains(&spill)
            || self.graph.blocks[spill].successors != [close]
            || cleanup_locals::store(store) != Some(local)
            || !target.exception_predecessors.is_empty()
            || target
                .predecessors
                .iter()
                .any(|pred| !scaffold.contains(pred))
            || local.slots().any(|slot| {
                slot == resource
                    || slot == primary
                    || ambient
                        .iter()
                        .any(|route| self.live_after(route.handler, slot))
            })
        {
            return None;
        }
        Some(Return {
            spill,
            block: next,
            transfer: target.instructions.end - 1,
        })
    }

    fn diamond(&self, head: usize) -> Result<Option<Match>, LiftError> {
        let Some((resource, continuation, primary_check)) = self.null_branch(head) else {
            return Ok(None);
        };
        let Some((primary, unguarded_close, guarded_close)) = self.null_branch(primary_check)
        else {
            return Ok(None);
        };
        let Some(close) = self.close(guarded_close, resource)? else {
            return Ok(None);
        };
        if self.close(unguarded_close, resource)? != Some(close) {
            return Ok(None);
        }
        let Some((guarded_goto, guarded_next)) = self.goto_after(guarded_close, 2) else {
            return Ok(None);
        };
        let Some((unguarded_goto, unguarded_next)) = self.goto_after(unguarded_close, 2) else {
            return Ok(None);
        };
        if guarded_next != continuation || unguarded_next != continuation {
            return Ok(None);
        }
        let Some(&suppression) = self.routes[guarded_close].first() else {
            return Ok(None);
        };
        if !self.throwable(suppression)? {
            return Ok(None);
        }
        let suppressed_code = self.block(suppression.handler);
        let [store, receiver, first, invoke, ..] = suppressed_code else {
            return Ok(None);
        };
        let Some(suppressed) = reference_store(store) else {
            return Ok(None);
        };
        if suppressed == resource
            || suppressed == primary
            || reference_load(receiver) != Some(primary)
            || reference_load(first) != Some(suppressed)
            || invoke.opcode != 0xb6
        {
            return Ok(None);
        }
        let Some(index) = invoke_index(invoke) else {
            return Ok(None);
        };
        if self.machine.exception_member(index)?
            != (
                "java/lang/Throwable",
                "addSuppressed",
                "(Ljava/lang/Throwable;)V",
            )
            || self.after_prefix(suppression.handler, 4) != Some(continuation)
        {
            return Ok(None);
        }
        let mut removed = BTreeSet::from([
            head,
            primary_check,
            guarded_close,
            unguarded_close,
            suppression.handler,
        ]);
        if removed.len() != 5 || removed.contains(&continuation) {
            return Ok(None);
        }
        for block in [guarded_goto, unguarded_goto].into_iter().flatten() {
            if !removed.insert(block) || block == continuation {
                return Ok(None);
            }
        }
        Ok(Some(Match {
            resource,
            primary,
            close,
            continuation,
            removed,
            suppression,
            suppressed,
        }))
    }

    fn closed_side(
        &self,
        side: &Match,
        head: usize,
        exceptional_entry: Option<usize>,
        body: &BTreeSet<usize>,
        ambient: &[Route],
    ) -> bool {
        let destination = side.suppression.handler;
        let mut supplier = None;
        for &block in &side.removed {
            let node = &self.graph.blocks[block];
            if self.routes[block].first() == Some(&side.suppression) {
                if supplier.replace(block).is_some() || &self.routes[block][1..] != ambient {
                    return false;
                }
            } else if self.routes[block] != ambient {
                return false;
            }
            if node.predecessors.iter().any(|pred| {
                !(side.removed.contains(pred)
                    || block == head && (body.contains(pred) || Some(*pred) == exceptional_entry))
            }) || node
                .successors
                .iter()
                .any(|next| !side.removed.contains(next) && *next != side.continuation)
            {
                return false;
            }
            if block != destination && !node.exception_predecessors.is_empty() {
                return false;
            }
        }
        supplier.is_some_and(|source| {
            self.graph.blocks[destination].exception_predecessors == [source]
                && self.graph.blocks[destination].predecessors.is_empty()
        })
    }

    fn throwable(&self, route: Route) -> Result<bool, LiftError> {
        Ok(route.catch_type != 0
            && self.machine.exception_class(route.catch_type)? == "java/lang/Throwable")
    }

    fn close(&self, block: usize, resource: u16) -> Result<Option<(u8, u16)>, LiftError> {
        let [load, invoke, ..] = self.block(block) else {
            return Ok(None);
        };
        let Some(index) = invoke_index(invoke) else {
            return Ok(None);
        };
        if reference_load(load) != Some(resource) || !matches!(invoke.opcode, 0xb6 | 0xb9) {
            return Ok(None);
        }
        let (owner, name, descriptor) = self.machine.exception_member(index)?;
        Ok(
            (name == "close" && descriptor == "()V" && self.machine.is_auto_closeable(owner))
                .then_some((invoke.opcode, index)),
        )
    }

    fn null_branch(&self, block: usize) -> Option<(u16, usize, usize)> {
        let [load, branch] = self.block(block) else {
            return None;
        };
        let &[taken, fallthrough] = self.graph.blocks[block].successors.as_slice() else {
            return None;
        };
        let slots = (reference_load(load)?, taken, fallthrough);
        (branch.opcode == 0xc6).then_some(slots)
    }

    fn goto_after(&self, block: usize, consumed: usize) -> Option<(Option<usize>, usize)> {
        let target = self.after_prefix(block, consumed)?;
        if self.block(block).len() == consumed
            && let [instruction] = self.block(target)
            && matches!(instruction.opcode, 0xa7 | 0xc8)
            && self.graph.blocks[target].predecessors == [block]
        {
            return self
                .after_prefix(target, 0)
                .map(|next| (Some(target), next));
        }
        Some((None, target))
    }

    fn after_prefix(&self, block: usize, consumed: usize) -> Option<usize> {
        let &[next] = self.graph.blocks[block].successors.as_slice() else {
            return None;
        };
        match self.block(block).get(consumed..)? {
            []
            | [
                Instruction {
                    opcode: 0xa7 | 0xc8,
                    ..
                },
            ] => Some(next),
            _ => None,
        }
    }

    fn block(&self, block: usize) -> &[Instruction] {
        &self.instructions[self.graph.blocks[block].instructions.clone()]
    }

    fn live_after(&self, entry: usize, slot: u16) -> bool {
        let mut seen = BTreeSet::new();
        let mut pending = vec![entry];
        while let Some(block) = pending.pop() {
            if !seen.insert(block) {
                continue;
            }
            let node = &self.graph.blocks[block];
            match self.block(block).iter().find(|op| local_touches(op, slot)) {
                Some(op) if matches!(op.opcode, 0x36..=0x4e) => {}
                Some(_) => return true,
                None => pending.extend(node.successors.iter().copied()),
            }
            pending.extend(node.exception_successors.iter().copied());
        }
        false
    }
}

fn invoke_index(instruction: &Instruction) -> Option<u16> {
    match instruction.operand {
        Operand::Constant(index) | Operand::InvokeInterface { index, .. } => Some(index),
        _ => None,
    }
}
