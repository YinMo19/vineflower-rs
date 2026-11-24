// Based on Vineflower's IfPatternMatchProcessor (Apache-2.0).
use std::{
    mem,
    ops::{Range, RangeInclusive},
};

use crate::{
    bytecode::{Instruction, Operand},
    descriptor::Type,
    lift::{Effect, IfPatternLocal, Machine},
};

use super::{Arm, Condition, Emitter, Region, StructureError, Tail, logical};

pub(super) struct Binding {
    success: usize,
    body_start: Option<usize>,
    locals: BoundLocals,
}

enum BoundLocals {
    Single(IfPatternLocal),
    Record(Vec<IfPatternLocal>),
}

impl BoundLocals {
    fn as_slice(&self) -> &[IfPatternLocal] {
        match self {
            Self::Single(local) => std::slice::from_ref(local),
            Self::Record(locals) => locals,
        }
    }
}

impl Binding {
    pub(super) fn record(success: usize, locals: Vec<IfPatternLocal>) -> Self {
        Self { success, body_start: None, locals: BoundLocals::Record(locals) }
    }

    fn locals_are_dead(&self, emitter: &mut Emitter<'_>, block: usize) -> bool {
        self.locals
            .as_slice()
            .iter()
            .all(|local| !emitter.local_is_live(block, local.slot()))
    }

    pub(super) fn succeeds_at(&self, block: usize) -> bool {
        self.success == block
    }

    pub(super) fn enter(&self, machine: &mut Machine<'_, '_>) -> Option<usize> {
        for local in self.locals.as_slice() {
            machine.install_if_pattern_local(local);
        }
        self.body_start
    }
}

struct Site {
    success: usize,
    beginning: usize,
    alias: Option<usize>,
    head_end: usize,
    load: usize,
    test: usize,
    cast: usize,
    store: usize,
    slot: u16,
    ty: Type,
}

/// The check and backing cast must read the same JVM definition, and only
/// the test's matching edge may enter the cast/store prologue.
pub(super) struct MatchPrologue {
    pub(super) success: usize,
    load: usize,
    cast: usize,
    store: usize,
    selector: u16,
    slot: u16,
    test_class: u16,
    cast_class: u16,
}

impl MatchPrologue {
    pub(super) fn body_start(&self) -> usize {
        self.store + 1
    }

    pub(super) fn instructions(&self) -> Range<usize> {
        self.cast - 1..self.body_start()
    }

    fn ty(&self, machine: &Machine<'_, '_>) -> Option<Type> {
        let ty = machine.pattern_class(self.test_class).ok()?;
        (machine.pattern_class(self.cast_class).ok()? == ty).then_some(ty)
    }
}

impl Emitter<'_> {
    pub(super) fn instanceof_prologue(&self, head: usize, first: usize) -> Option<MatchPrologue> {
        let block = &self.graph.blocks[head];
        let &[taken, fallthrough] = block.successors.as_slice() else { return None };
        let [.., load, test, branch] = &self.instructions[first..block.instructions.end] else { return None };
        let success = match branch.opcode {
            0x99 => fallthrough,
            0x9a => taken,
            _ => return None,
        };
        let next = &self.graph.blocks[success];
        if taken == fallthrough || next.predecessors != [head]
            || !block.exception_successors.is_empty()
            || !next.exception_predecessors.is_empty()
            || !next.exception_successors.is_empty()
        {
            return None;
        }
        let selector = reference_local(load, false)?;
        let [reload, cast, store, ..] = &self.instructions[next.instructions.clone()] else { return None };
        let slot = reference_local(store, true)?;
        if reference_local(reload, false) != Some(selector) || slot == selector {
            return None;
        }
        let (0xc1, Operand::Constant(test_class), 0xc0, Operand::Constant(cast_class)) =
            (test.opcode, &test.operand, cast.opcode, &cast.operand)
        else {
            return None;
        };
        let load = block.instructions.end - 3;
        let cast = next.instructions.start + 1;
        let store = cast + 1;
        if (load..block.instructions.end).chain(cast - 1..=store)
            .any(|index| self.exceptions.skips_instruction(index))
        {
            return None;
        }
        Some(MatchPrologue { success, load, cast, store, selector, slot, test_class: *test_class, cast_class: *cast_class })
    }

    pub(super) fn lift_guard_instanceof(
        &mut self,
        block: usize,
        first: usize,
        site: &MatchPrologue,
        machine: &mut Machine<'_, '_>,
    ) -> Option<IfPatternLocal> {
        if !machine.supports_instanceof_patterns() || !machine.this_is_initialized() {
            return None;
        }
        let ty = site.ty(machine)?;
        let end = self.instanceof_alias(block, first, site).filter(|&alias| {
            machine.if_pattern_alias_unnamed(&self.instructions[alias], site.selector)
        }).unwrap_or(site.load + 1);
        // Keep the expression on the stack in place of the private
        // astore/aload pair. Its evaluation remains on the matching path of
        // the preceding guard, and only the pattern test consumes it.
        for op in &self.instructions[first..end] {
            if !matches!(machine.step(op).ok()?, Effect::None) || !machine.take_prelude().is_empty() {
                return None;
            }
        }
        if !machine.if_pattern_selector(&ty) {
            return None;
        }
        let local = machine.prepare_guard_pattern_local(
            &ty, &self.instructions[site.cast], &self.instructions[site.store], site.slot,
        ).ok()??;
        machine.lift_if_pattern_test(&self.instructions[site.load + 1], &local).ok()?;
        Some(local)
    }

    fn instanceof_site(
        &mut self,
        head: usize,
        machine: &Machine<'_, '_>,
        region: Region<'_, '_, '_>,
        allowed_exit: Option<usize>,
    ) -> Option<Site> {
        if !machine.supports_instanceof_patterns()
            || !machine.this_is_initialized()
            || region.exception_arm.is_some()
            || region.protected.is_some()
            || self.assertion_starts(head)
        {
            return None;
        }
        let head_range = self.graph.blocks[head].instructions.clone();
        let site = self.instanceof_prologue(head, head_range.start)?;
        let success = site.success;
        if self.emitted[success]
            || (!self.layout.inside(success, region) && Some(success) != allowed_exit)
            || self.layout.loops[success].is_some()
            || self
                .exceptions
                .at_start(region.exception_arm, success)
                .is_some()
        {
            return None;
        }
        let ty = site.ty(machine)?;
        let alias = self.instanceof_alias(head, head_range.start, &site);
        Some(Site {
            success,
            beginning: head_range.start,
            alias,
            head_end: head_range.end,
            load: site.load,
            test: site.load + 1,
            cast: site.cast,
            store: site.store,
            slot: site.slot,
            ty,
        })
    }

    fn instanceof_alias(&mut self, head: usize, first: usize, site: &MatchPrologue) -> Option<usize> {
        // Javac often evaluates a selector once into an unnamed alias. Erase
        // that store only if neither edge can observe the slot before another
        // write. In particular, a second check or an escaping use keeps it.
        let alias = site.load.checked_sub(1).filter(|&index| {
            index >= first
                && reference_local(&self.instructions[index], true) == Some(site.selector)
                && !self.exceptions.skips_instruction(index)
        })?;
        let after = self.graph.blocks[site.success].instructions.end;
        let escapes = self.instructions[site.body_start()..after]
            .iter()
            .find_map(|instruction| local_access(instruction, site.selector))
            .unwrap_or_else(|| {
                // The prologue can share a block with the next condition.
                // If it does not access the alias, check every exit.
                let successors = self.graph.blocks[site.success].successors.as_slice();
                successors.iter().any(|&next| {
                    self.layout.local_is_live(self.graph, self.instructions, next, site.selector)
                })
            });
        let unmatched = *self.graph.blocks[head].successors.iter().find(|&&next| next != site.success)?;
        (!escapes && !self.local_is_live(unmatched, site.selector)).then_some(alias)
    }

    pub(super) fn lift_instanceof_head<'a, 'c>(
        &mut self,
        block: usize,
        machine: &mut Machine<'a, 'c>,
        region: Region<'_, 'a, 'c>,
        depth: usize,
        offsets: Vec<u32>,
    ) -> Result<(Tail, Option<Binding>), StructureError> {
        let site = (!self.has_record_instance(block))
            .then(|| self.instanceof_site(block, machine, region, None)).flatten();
        let Some(site) = site else {
            return Ok((
                self.lift_block(block, machine, region, depth, offsets)?,
                None,
            ));
        };
        self.lift_instanceof_site(block, site, machine, region, depth, offsets)
    }

    /// When the matching edge exits a negated loop, the binding can exist
    /// after source `while` only if all exits execute that test and the
    /// condition itself can become the loop header rather than a body guard.
    pub(super) fn lift_inverted_instanceof_loop_head<'a, 'c>(
        &mut self,
        block: usize,
        exit: usize,
        machine: &mut Machine<'a, 'c>,
        region: Region<'_, 'a, 'c>,
        depth: usize,
    ) -> Option<(Tail, Binding)> {
        if !machine.stack_is_empty() { return None; }
        let site = self.instanceof_site(block, machine, region, Some(exit)).filter(|site| site.success == exit)?;
        let names = machine.local_name_checkpoint();
        let start = self.lines.len();
        let mut trial = machine.clone();
        let lifted = self.lift_instanceof_site(block, site, &mut trial, region, depth, Vec::new());
        if let Ok((tail, Some(binding))) = lifted
            && self.lines.len() == start && trial.stack_is_empty()
            && trial.same_locals(machine) && trial.take_prelude().is_empty()
        {
            *machine = trial;
            return Some((tail, binding));
        }
        self.lines.truncate(start);
        machine.restore_local_names(names);
        None
    }

    fn lift_instanceof_site<'a, 'c>(
        &mut self,
        block: usize,
        site: Site,
        machine: &mut Machine<'a, 'c>,
        region: Region<'_, 'a, 'c>,
        depth: usize,
        offsets: Vec<u32>,
    ) -> Result<(Tail, Option<Binding>), StructureError> {
        let mut cursor = site.alias.unwrap_or(site.load + 1);
        let Tail {
            effect,
            mut offsets,
            ..
        } = self.lift_range(
            block,
            site.beginning..cursor,
            machine,
            region,
            depth,
            offsets,
        )?;
        if !matches!(effect, Effect::None) {
            return Err(self.unstructured(block));
        }
        let inline = site.alias.is_some_and(|alias| {
            let op = &self.instructions[alias];
            let slot = reference_local(op, true).expect("an alias is an astore");
            machine.if_pattern_alias_unnamed(op, slot) && machine.if_pattern_selector(&site.ty)
        });
        if !inline && cursor != site.load + 1 {
            let tail = self.lift_range(
                block,
                cursor..site.load + 1,
                machine,
                region,
                depth,
                offsets,
            )?;
            if !matches!(tail.effect, Effect::None) {
                return Err(self.unstructured(block));
            }
            offsets = tail.offsets;
            cursor = site.load + 1;
        }
        let cast = &self.instructions[site.cast];
        let store = &self.instructions[site.store];
        let local = if machine.if_pattern_selector(&site.ty) {
            machine.prepare_if_pattern_local(&site.ty, cast, store, site.slot)?
        } else {
            None
        };
        let Some(local) = local else {
            return Ok((
                self.lift_range(
                    block,
                    cursor..site.head_end,
                    machine,
                    region,
                    depth,
                    offsets,
                )?,
                None,
            ));
        };
        let test = &self.instructions[site.test];
        let branch = &self.instructions[site.test + 1];
        machine.lift_if_pattern_test(test, &local)?;
        let control = machine.control_order(branch)?;
        let effect = machine.step(branch)?;
        for instruction in self.instructions[cursor..site.head_end]
            .iter()
            .chain(&self.instructions[site.cast - 1..=site.store])
        {
            offsets.extend(instruction.offset..instruction.offset + instruction.len);
        }
        Ok((
            Tail {
                effect,
                offsets,
                control,
            },
            Some(Binding {
                success: site.success,
                body_start: Some(site.store + 1),
                locals: BoundLocals::Single(local),
            }),
        ))
    }

    /// Merge guards only along the uniquely-owned matching edge. The
    /// alternate edge must be the same edge as the failed type test, so the
    /// binding remains in scope for every reachable use after the guard.
    pub(super) fn collapse_instanceof_guard<'a, 'c>(
        &mut self,
        head: usize,
        region: Region<'_, 'a, 'c>,
        machine: &Machine<'a, 'c>,
        depth: usize,
        condition: &mut Condition,
        binding: &mut Binding,
        offsets: &mut Vec<u32>,
        control: &mut RangeInclusive<u32>,
    ) -> Result<bool, StructureError> {
        if matches!(binding.locals, BoundLocals::Single(_))
            && self.fold_instanceof_alternative(head, region, machine, depth, condition, binding, offsets, control)?
        {
            return Ok(false);
        }
        let mut folded = Vec::new();
        self.fold_instanceof_guards(
            head,
            region,
            machine,
            depth,
            condition,
            binding,
            offsets,
            control,
            None,
            &mut folded,
        )?;
        for block in folded {
            self.emitted[block] = true;
        }
        Ok(true)
    }

    /// Fold `match && guard || alternative` only when the shared success
    /// never reads the binding and every predecessor of the alternative is
    /// one of the false edges already represented by the guarded test.
    fn fold_instanceof_alternative<'a, 'c>(
        &mut self,
        head: usize,
        region: Region<'_, 'a, 'c>,
        machine: &Machine<'a, 'c>,
        depth: usize,
        condition: &mut Condition,
        binding: &mut Binding,
        offsets: &mut Vec<u32>,
        control: &mut RangeInclusive<u32>,
    ) -> Result<bool, StructureError> {
        let success_is_taken = binding.succeeds_at(condition.taken);
        let failure = if success_is_taken { condition.fallthrough } else { condition.taken };
        let alternative = &self.graph.blocks[failure];
        let guard = &self.graph.blocks[binding.success];
        let [taken, fallthrough] = *alternative.successors.as_slice() else { return Ok(false); };
        let (shared, unique) = match (guard.successors.contains(&taken), guard.successors.contains(&fallthrough)) {
            (true, false) => (taken, fallthrough),
            (false, true) => (fallthrough, taken),
            _ => return Ok(false),
        };
        if self.emitted[failure] || self.assertion_starts(failure)
            || !alternative.exception_predecessors.is_empty() || !alternative.exception_successors.is_empty()
            || !self.layout.inside(failure, region) || self.layout.loops[failure].is_some()
            || self.exceptions.at_start(region.exception_arm, failure).is_some()
        {
            return Ok(false);
        }
        let name_checkpoint = machine.local_name_checkpoint();
        let start = self.lines.len();
        let mut along = machine.clone();
        let tail = self.lift_block(failure, &mut along, region, depth, Vec::new());
        let has_lines = self.lines.len() != start;
        self.lines.truncate(start);
        let Ok(Tail {
            effect: Effect::Branch { target, when_true, when_false },
            offsets: rhs_offsets,
            control: Some(rhs_control),
        }) = tail else {
            machine.restore_local_names(name_checkpoint);
            return Ok(false);
        };
        if has_lines || !along.same_locals(machine) || !along.same_control_stack(machine) {
            machine.restore_local_names(name_checkpoint);
            return Ok(false);
        }
        let (taken, _) = self.branch_targets(failure, target)?;
        let (yes, no) = if taken == shared { (when_true, when_false) } else { (when_false, when_true) };
        let previous = (binding.success, binding.body_start);
        let mut trial = Condition {
            taken: condition.taken,
            fallthrough: condition.fallthrough,
            when_true: condition.when_true.clone(),
            when_false: condition.when_false.clone(),
        };
        let mut inner_control = control.clone();
        let mut inner_offsets = Vec::new();
        let mut folded = Vec::new();
        self.fold_instanceof_guards(head, region, machine, depth, &mut trial, binding,
            &mut inner_offsets, &mut inner_control, Some((failure, shared)), &mut folded)?;
        let closed = self.graph.blocks[failure].predecessors.iter()
            .all(|predecessor| *predecessor == head || folded.contains(predecessor));
        if !closed || binding.body_start.is_some() || !binding.succeeds_at(shared)
            || *rhs_control.start() <= *inner_control.end()
        {
            (binding.success, binding.body_start) = previous;
            machine.restore_local_names(name_checkpoint);
            return Ok(false);
        }
        if success_is_taken {
            trial.fallthrough = unique;
            trial.when_true = logical(trial.when_true, "||", yes);
            trial.when_false = logical(trial.when_false, "&&", no);
        } else {
            trial.taken = unique;
            trial.when_false = logical(trial.when_false, "||", yes);
            trial.when_true = logical(trial.when_true, "&&", no);
        }
        self.emitted[failure] = true;
        for block in folded { self.emitted[block] = true; }
        offsets.extend(inner_offsets);
        offsets.extend(rhs_offsets);
        *control = *control.start()..=*rhs_control.end();
        *condition = trial;
        Ok(true)
    }

    fn fold_instanceof_guards<'a, 'c>(
        &mut self,
        mut head: usize,
        region: Region<'_, 'a, 'c>,
        machine: &Machine<'a, 'c>,
        depth: usize,
        condition: &mut Condition,
        binding: &mut Binding,
        offsets: &mut Vec<u32>,
        control: &mut RangeInclusive<u32>,
        bypass: Option<(usize, usize)>,
        folded: &mut Vec<usize>,
    ) -> Result<(), StructureError> {
        let success_is_taken = binding.success == condition.taken;
        let failure = if success_is_taken {
            condition.fallthrough
        } else {
            condition.taken
        };
        loop {
            let next = binding.success;
            let node = &self.graph.blocks[next];
            if node.predecessors != [head]
                || !node.exception_predecessors.is_empty()
                || !node.exception_successors.is_empty()
                || node.successors.len() != 2
                || !node.successors.contains(&failure)
                || self.emitted[next]
                || self.assertion_starts(next)
                || self.layout.loops[next].is_some()
                || !self.layout.inside(next, region)
                || self
                    .exceptions
                    .at_start(region.exception_arm, next)
                    .is_some()
            {
                break;
            }
            let mut along = machine.clone();
            let start = binding.enter(&mut along).unwrap_or(node.instructions.start);
            let baseline = along.clone();
            let range = start..node.instructions.end;
            let name_checkpoint = machine.local_name_checkpoint();
            let start = self.lines.len();
            let tail = self.lift_range(next, range, &mut along, region, depth, Vec::new());
            let has_lines = self.lines.len() != start;
            self.lines.truncate(start);
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
                machine.restore_local_names(name_checkpoint);
                break;
            };
            if has_lines
                || !along.same_locals(&baseline)
                || !along.same_control_stack(&baseline)
                || *inner_control.start() <= *control.end()
            {
                machine.restore_local_names(name_checkpoint);
                break;
            }
            let (taken, fallthrough) = self.branch_targets(next, target)?;
            let (unique, yes, no) = if taken == failure {
                (fallthrough, when_false, when_true)
            } else {
                (taken, when_true, when_false)
            };
            // A third path into the surviving arm would not establish the
            // binding. Never infer scope from a shared successor alone.
            let survivor = &self.graph.blocks[unique];
            let owned = survivor.predecessors == [next];
            let bypasses_binding = bypass.is_some_and(|(outer, shared)| {
                shared == unique
                    && survivor.predecessors.len() == 2
                    && survivor.predecessors.contains(&next)
                    && survivor.predecessors.contains(&outer)
            }) && binding.locals_are_dead(self, unique);
            if !(owned || bypasses_binding)
                || !self.graph.blocks[unique].exception_predecessors.is_empty()
                || !self.layout.inside(unique, region)
            {
                machine.restore_local_names(name_checkpoint);
                break;
            }
            if success_is_taken {
                condition.taken = unique;
                condition.when_true = logical(mem::take(&mut condition.when_true), "&&", yes);
                condition.when_false = logical(mem::take(&mut condition.when_false), "||", no);
            } else {
                condition.fallthrough = unique;
                condition.when_false = logical(mem::take(&mut condition.when_false), "&&", yes);
                condition.when_true = logical(mem::take(&mut condition.when_true), "||", no);
            }
            folded.push(next);
            binding.success = unique;
            binding.body_start = None;
            head = next;
            offsets.extend(inner_offsets);
            *control = *control.start()..=*inner_control.end();
        }
        Ok(())
    }

    /// Factor a preceding `&&` or `||` into a pattern condition. A bypassed
    /// match can contribute to the condition, but cannot bind the local on
    /// a path that did not evaluate the type test.
    pub(super) fn collapse_instanceof_prefix<'a, 'c>(
        &mut self,
        head: usize,
        region: Region<'_, 'a, 'c>,
        machine: &Machine<'a, 'c>,
        depth: usize,
        condition: &mut Condition,
        offsets: &mut Vec<u32>,
        control: &mut RangeInclusive<u32>,
    ) -> Result<Option<Option<Binding>>, StructureError> {
        if condition.taken == condition.fallthrough {
            return Ok(None);
        }
        for (next, shared) in [
            (condition.fallthrough, condition.taken),
            (condition.taken, condition.fallthrough),
        ] {
            let node = &self.graph.blocks[next];
            if node.predecessors != [head]
                || node.successors.len() != 2
                || !node.exception_predecessors.is_empty()
                || self.emitted[next]
                || self.layout.loops[next].is_some()
                || !self.layout.inside(next, region)
                || self
                    .exceptions
                    .at_start(region.exception_arm, next)
                    .is_some()
                || self.instanceof_site(next, machine, region, None).is_none()
            {
                continue;
            }
            let name_checkpoint = machine.local_name_checkpoint();
            let start = self.lines.len();
            let mut along = machine.clone();
            let tail = self.lift_instanceof_head(next, &mut along, region, depth, Vec::new());
            let has_lines = self.lines.len() != start;
            self.lines.truncate(start);
            let Ok((
                Tail {
                    effect:
                        Effect::Branch {
                            target,
                            when_true,
                            when_false,
                        },
                    offsets: mut inner_offsets,
                    control: Some(mut inner_control),
                },
                Some(mut binding),
            )) = tail
            else {
                machine.restore_local_names(name_checkpoint);
                continue;
            };
            if has_lines
                || !along.same_locals(machine)
                || !along.same_control_stack(machine)
                || *inner_control.start() <= *control.end()
            {
                machine.restore_local_names(name_checkpoint);
                continue;
            }
            let (taken, fallthrough) = self.branch_targets(next, target)?;
            let mut inner = Condition {
                taken,
                fallthrough,
                when_true,
                when_false,
            };
            let mut folded = Vec::new();
            self.fold_instanceof_guards(
                next,
                region,
                machine,
                depth,
                &mut inner,
                &mut binding,
                &mut inner_offsets,
                &mut inner_control,
                Some((head, shared)),
                &mut folded,
            )?;
            let Condition {
                taken,
                fallthrough,
                when_true,
                when_false,
            } = inner;
            let (unique, yes, no) = if taken == shared {
                (fallthrough, when_false, when_true)
            } else if fallthrough == shared {
                (taken, when_true, when_false)
            } else {
                machine.restore_local_names(name_checkpoint);
                continue;
            };
            let binding = if binding.succeeds_at(unique) {
                Some(binding)
            } else if binding.body_start.is_none()
                && binding.locals_are_dead(self, shared)
            {
                None
            } else {
                machine.restore_local_names(name_checkpoint);
                continue;
            };
            if next == condition.taken {
                condition.taken = unique;
                condition.when_true = logical(mem::take(&mut condition.when_true), "&&", yes);
                condition.when_false = logical(mem::take(&mut condition.when_false), "||", no);
            } else {
                condition.fallthrough = unique;
                condition.when_false = logical(mem::take(&mut condition.when_false), "&&", yes);
                condition.when_true = logical(mem::take(&mut condition.when_true), "||", no);
            }
            self.emitted[next] = true;
            for block in folded {
                self.emitted[block] = true;
            }
            offsets.extend(inner_offsets);
            *control = *control.start()..=*inner_control.end();
            return Ok(Some(binding));
        }
        Ok(None)
    }

    pub(super) fn instanceof_join(
        &self,
        join: Option<usize>,
        region: Region<'_, '_, '_>,
        binding: Option<&Binding>,
    ) -> Option<usize> {
        // The success node is not a shared join. An abrupt sibling can make
        // the generic if recognizer pick it as the next block, so keep the
        // matching path in the arm which owns its declaration instead.
        if binding.is_some_and(|binding| join == Some(binding.success)) {
            region.stop
        } else {
            join
        }
    }

    pub(super) fn instanceof_empty_arm(
        &self,
        binding: Option<&Binding>,
        join: Option<usize>,
        arm: usize,
    ) -> bool {
        let Some(binding) = binding.filter(|binding| binding.success == arm) else {
            return false;
        };
        let block = &self.graph.blocks[binding.success];
        let start = binding.body_start.unwrap_or(block.instructions.start);
        let no_body = match &self.instructions[start..block.instructions.end] {
            [] => true,
            [op] => matches!(op.opcode, 0xa7 | 0xc8),
            _ => false,
        };
        no_body && matches!(block.successors.as_slice(), [only] if Some(*only) == join)
    }

    pub(super) fn instanceof_branch_arm<'a, 'c>(
        &mut self,
        start: usize,
        region: Region<'_, 'a, 'c>,
        baseline: &Machine<'a, 'c>,
        depth: usize,
        binding: Option<&Binding>,
    ) -> Result<Arm<'a, 'c>, StructureError> {
        let Some(binding) = binding.filter(|binding| binding.success == start) else {
            return self.branch_arm(start, region, baseline, depth);
        };
        let first_line = self.lines.len();
        let mut body = baseline.clone();
        let body_start = binding.enter(&mut body);
        let mut offsets = Vec::new();
        let reaches = self.run_region(
            start,
            region,
            &mut body,
            depth,
            &mut offsets,
            false,
            body_start,
        )?;
        if reaches {
            let stop = region.stop.expect("branch reached its stop");
            for local in binding.locals.as_slice() {
                if !self.local_is_live(stop, local.slot()) {
                    body.restore_if_pattern_slot(baseline, local);
                }
            }
        }
        Ok(Arm {
            exit: reaches.then_some(body),
            offsets,
            start: first_line,
            end: self.lines.len(),
        })
    }

    pub(super) fn lift_if_arm_start<'a, 'c>(
        &mut self,
        block: usize,
        start: usize,
        machine: &mut Machine<'a, 'c>,
        region: Region<'_, 'a, 'c>,
        depth: usize,
        offsets: Vec<u32>,
    ) -> Result<Tail, StructureError> {
        let mut range: Range<usize> = self.graph.blocks[block].instructions.clone();
        self.exception_range(block, region, &mut range)?;
        self.lift_range(block, start..range.end, machine, region, depth, offsets)
    }
}

fn reference_local(instruction: &Instruction, store: bool) -> Option<u16> {
    let (wide, compact) = if store { (0x3a, 0x4b) } else { (0x19, 0x2a) };
    match (instruction.opcode, &instruction.operand) {
        (opcode, Operand::Local(slot)) if opcode == wide => Some(*slot),
        (opcode, _) if (compact..compact + 4).contains(&opcode) => {
            Some(u16::from(opcode - compact))
        }
        _ => None,
    }
}

/// Classify an access by whether it reads the current binding before writing.
fn local_access(instruction: &Instruction, slot: u16) -> Option<bool> {
    let (index, read, wide_write) = match (instruction.opcode, &instruction.operand) {
        (0x15..=0x19 | 0xa9, Operand::Local(index)) => (*index, true, false),
        (op @ 0x1a..=0x2d, _) => (u16::from((op - 0x1a) % 4), true, false),
        (op @ 0x36..=0x3a, Operand::Local(index)) => (*index, false, matches!(op, 0x37 | 0x39)),
        (op @ 0x3b..=0x4e, _) => (
            u16::from((op - 0x3b) % 4),
            false,
            matches!((op - 0x3b) / 4, 1 | 3),
        ),
        (0x84, Operand::Increment { index, .. }) => (*index, true, false),
        _ => return None,
    };
    (slot == index || wide_write && index.checked_add(1) == Some(slot)).then_some(read)
}
