// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use crate::lift::Machine;

use super::{
    CloseExit, ClosePattern, Emitter, ExceptionRedirect, NormalExits, ProtectedRegion, Region,
    ResourceExit, StructureError,
};

impl Emitter<'_> {
    // Every normal edge must implement this exact close. Continuations may
    // share one target; a typed return instead belongs to its own spill and
    // reload. Never redirect a copied close into a differently protected arm.
    pub(super) fn prove_split_resource_exits(
        &mut self,
        shape: &ProtectedRegion,
        region: Region<'_, '_, '_>,
        machine: &Machine<'_, '_>,
        primary: usize,
        pattern: ClosePattern,
        skipped: &mut Vec<usize>,
    ) -> Result<Option<NormalExits>, StructureError> {
        let mut ambient = None;
        let mut continuation = None;
        let mut enclosing_terminal = None;
        let mut redirects = Vec::new();
        let mut terminal_blocks = Vec::new();
        for entry in shape.join.into_iter().chain(shape.split_resource_exits.iter().copied()) {
            let Some((close, exit)) = self.match_normal_resource_close(
                entry, pattern.slot, pattern.nullable, pattern.member, machine,
            )? else {
                return Ok(None);
            };
            let reference = *ambient.get_or_insert(close);
            if skipped.contains(&entry)
                || skipped.contains(&close)
                || self.graph.blocks[entry].predecessors.iter().any(|&pred| {
                    !self.exceptions.contains(Some(shape.body), pred)
                })
                || (entry != close && self.graph.blocks[close].predecessors != [entry])
                || self.graph.blocks[close].exception_successors
                    != self.graph.blocks[reference].exception_successors
                || !self.exceptions.matches_dispatch(close, reference, None)
                || self.exceptions.at_start(region.exception_arm, entry).is_some()
                || self.exceptions.at_start(region.exception_arm, close).is_some()
            {
                return Ok(None);
            }
            if entry != close {
                skipped.push(entry);
            }
            skipped.push(close);

            let edge = match exit {
                CloseExit::Continue(target) => {
                    let enclosing = self.exceptions.enclosing_terminal_copy(region.exception_arm, target);
                    let target = enclosing.unwrap_or(target);
                    if (enclosing.is_some() && region.stop != enclosing)
                        || enclosing_terminal.is_some_and(|previous| previous != enclosing)
                    {
                        return Ok(None);
                    }
                    enclosing_terminal = Some(enclosing);
                    if continuation.is_some_and(|previous| previous != target) {
                        return Ok(None);
                    }
                    continuation = Some(target);
                    ExceptionRedirect::Continue { target, arm: shape.body }
                }
                CloseExit::Return { block, transfer, local } => {
                    let Some((spill, store)) = self.exclusive_resource_spill(shape, entry, local)
                    else {
                        return Ok(None);
                    };
                    if self.protected_resource_slot_overlap(local, close, primary) {
                        return Ok(None);
                    }
                    if block != close {
                        if skipped.contains(&block)
                            || self.graph.blocks[block].predecessors.iter().any(|&pred| {
                                pred != entry && pred != close
                            })
                        {
                            return Ok(None);
                        }
                        skipped.push(block);
                        terminal_blocks.push(block);
                    }
                    redirects.push((spill, ExceptionRedirect::ReturnSpill { store, arm: shape.body }));
                    ExceptionRedirect::ReturnAtEdge { transfer, arm: shape.body }
                }
            };
            redirects.push((entry, edge));
        }
        if let Some(next) = continuation
            && (skipped.contains(&next)
                || self.exceptions.contains(Some(shape.body), next)
                || (!self.exceptions.contains(region.exception_arm, next)
                    && enclosing_terminal.flatten() != Some(next))
                || self.exceptions.at_start(region.exception_arm, next).is_some()
                || self.exceptions.bypass_cleanup(next) != next
                || self.layout.loops[next].is_some()
                || region.loop_transfer(next).is_some()
                || !self.graph.blocks[next].exception_predecessors.is_empty()
                || self.layout.local_is_live(self.graph, self.instructions, next, pattern.slot))
        {
            return Ok(None);
        }
        Ok(ambient.map(|close| NormalExits {
            close,
            stop: continuation,
            exit: ResourceExit::Continue(continuation),
            redirects,
            terminal_blocks,
            fulfilled_return: None,
        }))
    }
}
