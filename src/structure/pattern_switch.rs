// Copyright 2000-2024 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use std::{
    collections::{BTreeMap, BTreeSet, HashSet},
    mem,
    ops::Range,
};

use crate::{
    bytecode::{Instruction, Operand},
    classfile::{Constant, ConstantPool},
    descriptor::Type,
    lift::{Effect, Machine, pattern_dispatch::PatternLabel},
    source_text::Document,
};

use super::{Emitter, Line, Region, StructureError, switch_expression::CaseLabel};

#[path = "pattern_guard.rs"]
mod guards;

#[path = "pattern_value.rs"]
mod values;

#[cfg(test)]
#[path = "pattern_guard_tests.rs"]
mod regressions;

pub(super) struct Head {
    /// The suffix replaced by the source switch, excluding selector evaluation.
    setup: usize,
    restart: u16,
    restart_store: Option<usize>,
    alias_store: usize,
    alias: u16,
    null_check: bool,
}

impl Head {
    pub(super) fn recognize(
        instructions: &[Instruction],
        range: Range<usize>,
        pool: &ConstantPool<'_>,
    ) -> Option<Self> {
        let dyn_index = range.end.checked_sub(2)?;
        if dyn_index < range.start
            || instructions[dyn_index].opcode != 0xba
            || !matches!(instructions[range.end - 1].operand, Operand::Switch { .. })
        {
            return None;
        }
        // Javac stores the selector in a private temporary and starts the
        // search from zero, either through an int local or directly.
        let tail = instructions.get(range.start..dyn_index)?;
        let restart_op = tail.last()?;
        let (alias_op, alias_store, restart, restart_store) = if push_zero(restart_op) {
            (
                tail.get(tail.len().checked_sub(2)?)?,
                tail.get(tail.len().checked_sub(3)?)?,
                0,
                None,
            )
        } else {
            let restart = local(restart_op, false, false)?;
            let [.., alias_store, zero, store, alias_op, _] = tail else {
                return None;
            };
            if !push_zero(zero) || local(store, true, false) != Some(restart) {
                return None;
            }
            (alias_op, alias_store, restart, Some(dyn_index - 3))
        };
        let alias = local(alias_op, false, true)?;
        if local(alias_store, true, true) != Some(alias)
            || restart_store.is_some() && restart == alias
        {
            return None;
        }
        let mut setup = dyn_index - if restart_store.is_some() { 5 } else { 3 };
        let null_check = ends_with_null_check(instructions.get(range.start..setup)?, pool);
        if null_check {
            setup -= 3;
        }
        Some(Self {
            setup,
            restart,
            alias_store: dyn_index - if restart_store.is_some() { 5 } else { 3 },
            restart_store,
            alias,
            null_check,
        })
    }

    pub(super) fn alias(&self) -> u16 {
        self.alias
    }
}

fn ends_with_null_check(instructions: &[Instruction], pool: &ConstantPool<'_>) -> bool {
    let [.., dup, call, pop] = instructions else {
        return false;
    };
    if (dup.opcode, call.opcode, pop.opcode) != (0x59, 0xb8, 0x57) {
        return false;
    }
    let Operand::Constant(index) = call.operand else {
        return false;
    };
    matches!(pool.get(index), Ok(Constant::Methodref { .. }))
        && matches!(
            pool.member_ref(index),
            Ok((
                "java/util/Objects",
                "requireNonNull",
                "(Ljava/lang/Object;)Ljava/lang/Object;"
            ))
        )
}

pub(super) fn push_zero(op: &Instruction) -> bool {
    op.opcode == 0x03
        || matches!(
            (op.opcode, &op.operand),
            (0x10 | 0x11, Operand::Immediate(0))
        )
}

pub(super) fn local(op: &Instruction, store: bool, reference: bool) -> Option<u16> {
    let (wide, short) = match (store, reference) {
        (false, false) => (0x15, 0x1a),
        (false, true) => (0x19, 0x2a),
        (true, false) => (0x36, 0x3b),
        (true, true) => (0x3a, 0x4b),
    };
    match op.operand {
        Operand::Local(slot) if op.opcode == wide => Some(slot),
        _ if (short..short + 4).contains(&op.opcode) => Some(u16::from(op.opcode - short)),
        _ => None,
    }
}

fn touches_slot(op: &Instruction, slot: u16) -> bool {
    let (index, wide) = match (op.opcode, &op.operand) {
        (0x15..=0x19 | 0x36..=0x3a | 0xa9, Operand::Local(index)) => {
            (*index, matches!(op.opcode, 0x16 | 0x18 | 0x37 | 0x39))
        }
        (0x1a..=0x2d | 0x3b..=0x4e, _) => {
            let relative = op.opcode - if op.opcode <= 0x2d { 0x1a } else { 0x3b };
            (u16::from(relative % 4), matches!(relative / 4, 1 | 3))
        }
        (0x84, Operand::Increment { index, .. }) => (*index, false),
        _ => return false,
    };
    slot == index || wide && index.checked_add(1) == Some(slot)
}

const NULL_KEY: i32 = -1;

#[derive(Default)]
struct Arm {
    keys: Vec<i32>,
    /// The recognized `aload alias; [checkcast T;] astore local` prologue.
    binding: Option<(Range<usize>, u16)>,
    /// Javac 17 enumSwitch erases the source pattern type to the enum class.
    enum_pattern_type: Option<Type>,
    guard: Option<guards::Guard>,
    nullable_type: bool,
}

struct BoundArm<'a, 'c> {
    entry: Machine<'a, 'c>,
    labels: Vec<CaseLabel>,
}

impl Emitter<'_> {
    pub(super) fn try_emit_pattern_switch<'a, 'c>(
        &mut self,
        block: usize,
        region: Region<'_, 'a, 'c>,
        machine: &mut Machine<'a, 'c>,
        depth: usize,
        pending: &mut Vec<u32>,
        resume: &mut Option<usize>,
    ) -> Result<Option<Option<usize>>, StructureError> {
        let range = self.graph.blocks[block].instructions.clone();
        if range.is_empty()
            || region.exception_arm.is_some()
            || region.protected.is_some()
            || !self.graph.blocks[block].exception_successors.is_empty()
        {
            return Ok(None);
        }
        let (head, restart) = if let Some(head) = Head::recognize(self.instructions, range.clone(), machine.constant_pool()) {
            (head, None)
        } else if let Some((head, proof)) = guards::RestartLoop::recognize(self, block, machine.constant_pool()) {
            (head, Some(proof))
        } else {
            return Ok(None);
        };
        let dispatch_block = restart.as_ref().map_or(block, |proof| proof.dispatch);
        let indy = self.graph.blocks[dispatch_block].instructions.end - 2;
        let switch = &self.instructions[indy + 1];
        let Some(dispatch) = machine.read_pattern_dispatch(&self.instructions[indy])? else {
            return Ok(None);
        };
        let preview_enum = dispatch.is_enum() && machine.is_first_pattern_preview();
        let mut constants = HashSet::new();
        if dispatch.labels.iter().any(|label| !matches!(label, PatternLabel::Type(_)) && !constants.insert(label)) {
            return Ok(None);
        }
        let Operand::Switch { default, cases } = &switch.operand else {
            unreachable!()
        };
        let Some(default) = self.graph.block_at(*default) else {
            return Ok(None);
        };
        let mut groups = BTreeMap::<usize, Arm>::new();
        groups.entry(default).or_default();
        let mut by_key = vec![None; dispatch.labels.len()];
        let mut null_target = None;
        for &(key, target) in cases {
            let Some(target) = self.graph.block_at(target) else {
                return Ok(None);
            };
            match key {
                NULL_KEY => {
                    if null_target.replace(target).is_some() {
                        return Ok(None);
                    }
                }
                k if k >= 0 && (k as usize) < by_key.len() => {
                    if by_key[k as usize].replace(target).is_some() {
                        return Ok(None);
                    }
                }
                k if k == by_key.len() as i32 && target == default => {}
                _ if switch.opcode == 0xaa && target == default => {} // tableswitch padding
                _ => return Ok(None),
            }
        }
        let mut total_key = None;
        let mut latest_type_key = None;
        for (key, target) in by_key.into_iter().enumerate() {
            let key = key as i32;
            let type_label = matches!(dispatch.labels[key as usize], PatternLabel::Type(_));
            if type_label {
                latest_type_key = Some(key);
            }
            // Javac 17 lowers a final total pattern through the JVM default,
            // omitting its ordinary key when it would share the same target.
            // No other bootstrap label may implicitly alias the default.
            let target = if let Some(target) = target.filter(|&target| target != default) {
                target
            } else if key as usize + 1 == dispatch.labels.len()
                && type_label
                && machine.is_first_pattern_preview()
                && !head.null_check
                && null_target.unwrap_or(default) == default
            {
                total_key = Some(key);
                default
            } else {
                return Ok(None);
            };
            let keys = &mut groups.entry(target).or_default().keys;
            if keys.first().zip(latest_type_key).is_some_and(|(&first, type_key)| first < type_key) {
                // One source arm cannot put its constants on both sides of
                // a type test or its guard without changing priority.
                return Ok(None);
            }
            keys.push(key);
        }
        let source_default = total_key.is_none().then_some(default);
        if !head.null_check && total_key.is_none() {
            // Even when the integer switch omits -1, the bootstrap gives null
            // to its default arm, unlike a Java switch without a null label.
            let target = null_target.unwrap_or(default);
            groups.entry(target).or_default().keys.push(NULL_KEY);
        } else if null_target.is_some_and(|target| target != default) {
            return Ok(None);
        }

        let mut alias_uses = BTreeSet::from([indy - 2, head.alias_store]);
        let targets: BTreeSet<_> = groups.keys().copied().collect();
        for (&target, arm) in &mut groups {
            let cfg = &self.graph.blocks[target];
            if !cfg.exception_predecessors.is_empty()
                || !cfg.predecessors.contains(&dispatch_block)
                || Some(target) != source_default && cfg.predecessors != [dispatch_block]
            {
                return Ok(None);
            }
            let (key, ty) = match arm.keys.as_slice() {
                &[key] if key != NULL_KEY => match &dispatch.labels[key as usize] {
                    PatternLabel::Type(ty) => (key, ty),
                    _ => continue,
                },
                &[key, NULL_KEY] if null_target == Some(target) && machine.is_first_pattern_preview() => {
                    match &dispatch.labels[key as usize] {
                        PatternLabel::Type(ty) => {
                            arm.nullable_type = true;
                            (key, ty)
                        }
                        _ => continue,
                    }
                }
                keys if keys.iter().any(|&key| key != NULL_KEY
                    && matches!(dispatch.labels[key as usize], PatternLabel::Type(_))) => return Ok(None),
                _ => continue,
            };
            let mut body_start = cfg.instructions.start;
            let body = &self.instructions[cfg.instructions.clone()];
            if body
                .first()
                .is_some_and(|op| local(op, false, true) == Some(head.alias))
            {
                let (width, slot, cast_type) = match body {
                    [_, cast, store, ..] if cast.opcode == 0xc0 => {
                        let Operand::Constant(index) = cast.operand else {
                            return Ok(None);
                        };
                        let cast_type = machine.pattern_class(index)?;
                        if !preview_enum && cast_type != *ty {
                            return Ok(None);
                        }
                        let Some(slot) = local(store, true, true) else {
                            return Ok(None);
                        };
                        (3, slot, Some(cast_type))
                    }
                    [_, store, ..] => {
                        let Some(slot) = local(store, true, true) else {
                            return Ok(None);
                        };
                        (2, slot, None)
                    }
                    _ => return Ok(None),
                };
                if slot == head.alias || head.restart_store.is_some() && slot == head.restart {
                    return Ok(None);
                }
                if preview_enum {
                    let store = &body[width - 1];
                    arm.enum_pattern_type = machine.preview_enum_pattern_type(ty, cast_type, store, slot)?;
                    if arm.enum_pattern_type.is_none() {
                        return Ok(None);
                    }
                }
                alias_uses.insert(cfg.instructions.start);
                arm.binding = Some((cfg.instructions.start..cfg.instructions.start + width, slot));
                body_start += width;
            }
            if preview_enum && arm.binding.is_none() {
                return Ok(None);
            }
            if let Some(proof) = &restart {
                let Some(guard) = proof.arm(self, target, body_start, key, &targets) else {
                    return Ok(None);
                };
                if guard.as_ref().is_some_and(|guard| guard.success().is_none())
                    && machine.pattern_guard_keyword() != Some(" && ")
                {
                    // Final Java rejects guards that are constant false.
                    return Ok(None);
                }
                arm.guard = guard;
            }
            if (arm.nullable_type || total_key == Some(key)) && (arm.binding.is_none() || arm.guard.is_some()) {
                // The shared entry must bind the original selector as-is:
                // checkcast permits null, and no retry may rematch that null.
                return Ok(None);
            }
        }
        // Only a genuinely unconditional pattern can dominate later labels
        // or conflict with default. For enumSwitch use the proved source type.
        let pattern_types: Vec<_> = groups.iter().filter_map(|(&target, arm)| {
            let &key = arm.keys.first().filter(|&&key| key != NULL_KEY)?;
            let PatternLabel::Type(ty) = &dispatch.labels[key as usize] else { return None };
            let record = self.record_patterns.and_then(|plans| plans.get(switch.offset, self.offset(target)));
            (arm.guard.is_none() && !record.is_some_and(|record| record.may_fail))
                .then_some((key, arm.enum_pattern_type.as_ref().unwrap_or(ty)))
        }).collect();
        for arm in groups.values() {
            for &key in &arm.keys {
                if key != NULL_KEY
                    && let PatternLabel::Type(ty) = &dispatch.labels[key as usize]
                    && pattern_types.iter().any(|&(earlier, prior)| {
                        earlier < key && machine.pattern_covers(prior, arm.enum_pattern_type.as_ref().unwrap_or(ty))
                    })
                {
                    return Ok(None);
                }
            }
        }
        if restart.as_ref().is_some_and(|proof| !proof.owns_all_retries(groups.values().filter_map(|arm| arm.guard.as_ref()))) {
            return Ok(None);
        }
        if self.instructions.iter().enumerate().any(|(index, op)| {
            touches_slot(op, head.alias) && !alias_uses.contains(&index)
                || head.restart_store.is_some_and(|store| {
                    touches_slot(op, head.restart) && index != store && index != indy - 1
                        && !restart.as_ref().is_some_and(|proof| proof.restart_store(index))
                })
        }) {
            return Ok(None);
        }

        // The bytecode retry loop owns these blocks in the CFG, but the
        // source switch must still see only the real enclosing loop.
        let within = if restart.is_some() {
            region.with_exception_layout(Some(dispatch_block))
        } else {
            region
        };
        let join = restart.as_ref().and_then(|_| self.layout.loops[dispatch_block].and_then(|shape| shape.exit))
            .or_else(|| self.layout.normal_join(dispatch_block, within))
            .or_else(|| self.layout.common_join(
                self.graph, within,
                groups.iter().filter_map(|(&target, arm)| {
                    let entry = match &arm.guard {
                        Some(guard) => guard.success()?,
                        None => target,
                    };
                    Some((entry, None))
                }),
            ))
            .or(region.stop);
        if groups.keys().any(|&target| Some(target) == join && Some(target) != source_default)
            || join != source_default && self.graph.blocks[default].predecessors != [dispatch_block]
        {
            return Ok(None);
        }

        self.emitted[block] = true;
        let tail = self.lift_range(
            block,
            range.start..head.setup,
            machine,
            region,
            depth,
            mem::take(pending),
        )?;
        if !matches!(tail.effect, Effect::None) {
            return Err(self.unstructured(block));
        }
        let mut offsets = tail.offsets;
        let total = total_key.map(|key| match &dispatch.labels[key as usize] {
            PatternLabel::Type(ty) => groups[&default].enum_pattern_type.as_ref().unwrap_or(ty),
            _ => unreachable!("checked total label"),
        });
        let (selector, selector_type, control) = machine.take_pattern_selector(
            &self.instructions[indy],
            &dispatch,
            total,
            switch.offset + switch.len - 1,
        )?;
        if pattern_types.iter().any(|&(key, ty)| Some(key) != total_key && machine.pattern_covers(ty, &selector_type)) {
            // A source default conflicts with a total pattern, and a total
            // pattern before the final one would dominate it.
            return Err(self.unstructured(dispatch_block));
        }
        let switch_region = within.switch_body(join);
        let mut ordered: Vec<_> = groups.into_iter().collect();
        // Preserve the bootstrap matching order even if the bytecode lays
        // the switch blocks out differently. Null never competes with a type.
        ordered.sort_by_key(|(target, arm)| {
            if Some(*target) == source_default {
                (2, 0)
            } else if arm.keys == [NULL_KEY] {
                (0, 0)
            } else {
                (1, arm.keys.first().copied().unwrap_or_default())
            }
        });
        let guard_keyword = machine.pattern_guard_keyword().ok_or_else(|| self.unstructured(block))?;
        let mut staged = Vec::with_capacity(ordered.len());
        let names = machine.local_name_checkpoint();
        let anonymous = machine.switch_anonymous_checkpoint();
        let baseline = machine.switch_arm_entry(&control)?;
        let trial = (|| {
            for (target, arm) in &ordered {
                let mut entry = baseline.clone();
                let mut binding_offsets = Vec::new();
                let mut labels: Vec<CaseLabel> = Vec::with_capacity(arm.keys.len());
                if let Some((indices, _)) = &arm.binding {
                    let store = &self.instructions[indices.end - 1];
                    binding_offsets.extend(store.offset..store.offset + store.len);
                }
                let record = self.record_patterns.and_then(|plans| plans.get(switch.offset, self.offset(*target)));
                if let Some(record) = record {
                    binding_offsets.extend(&record.offsets);
                }
                for &key in &arm.keys {
                    if arm.nullable_type && key == NULL_KEY {
                        continue;
                    }
                    if key == NULL_KEY && entry.is_first_pattern_preview()
                        && let Some(last) = labels.last_mut()
                    {
                        last.text.push_str(", null");
                        continue;
                    }
                    let mut label: Document = if let Some(record) = record {
                        record.render(&mut entry)?
                    } else if key == NULL_KEY {
                        "null".into()
                    } else {
                        match &dispatch.labels[key as usize] {
                            PatternLabel::Type(ty) => entry.pattern_binding(
                                arm.enum_pattern_type.as_ref().unwrap_or(ty),
                                Some(&selector_type),
                                arm.binding.as_ref().map(|(indices, slot)| {
                                    (
                                        &self.instructions[indices.end - 1],
                                        (indices.len() == 3).then(|| &self.instructions[indices.start + 1]),
                                        *slot,
                                    )
                                }),
                                self.offset(*target),
                            )?,
                            constant => entry.pattern_constant(&dispatch, constant, &selector_type),
                        }
                    };
                    if arm.nullable_type {
                        label.surround("null, ", "");
                    }
                    if let Some(guard) = &arm.guard {
                        let first = arm.binding.as_ref().map_or(
                            self.graph.blocks[*target].instructions.start, |(indices, _)| indices.end,
                        );
                        let mut predicate = guard.document(self, first, &entry).ok_or_else(|| self.unstructured(*target))?;
                        if guard_keyword == " && " {
                            predicate.surround("(", ")");
                        }
                        label.push_str(guard_keyword);
                        label.append(predicate);
                    }
                    labels.push(CaseLabel { text: label, offsets: mem::take(&mut binding_offsets) });
                }
                staged.push(BoundArm { entry, labels });
            }
            Ok::<(), StructureError>(())
        })();
        if let Err(error) = trial {
            machine.restore_local_names(names);
            machine.restore_switch_anonymous_sites(anonymous);
            return Err(error);
        }
        if let Some(plans) = self.record_patterns {
            for (target, _) in &ordered {
                plans.claim(switch.offset, self.offset(*target));
            }
        }
        machine.commit_switch_dynamic_helpers(&baseline);
        offsets.extend(switch.offset..switch.offset + switch.len);
        let constructor_setup = machine.has_constructor_switch_receiver().then_some(head.setup);
        if let Some(setup) = constructor_setup
            && restart.is_none() && head.null_check && cases.is_empty()
            && let Some((target, start)) = self.try_default_switch_arm(
                dispatch_block, default, region, machine, depth, &selector, &control, Some(setup),
            )
        {
            *resume = Some(start);
            *pending = offsets;
            return Ok(Some(Some(target)));
        }
        if (restart.is_none() || constructor_setup.is_some())
            && let Some(join) = join
            && self.try_pattern_switch_value(
                dispatch_block, within, machine, depth, &selector, &ordered, &staged, source_default, join,
                &control, constructor_setup,
            )
        {
            self.mark_pattern_dispatch(dispatch_block, &ordered)?;
            *pending = offsets;
            return Ok(Some(Some(join)));
        }
        if !machine.stack_is_empty() {
            return Err(self.unstructured(block));
        }
        self.mark_pattern_dispatch(dispatch_block, &ordered)?;
        for statement in machine.take_prelude() {
            self.push(depth, statement, mem::take(&mut offsets));
        }
        let start = self.lines.len();
        self.push(
            depth,
            super::surrounded(selector, "switch (", ") {"),
            offsets,
        );
        let mut live = Vec::new();
        let return_join = join.filter(|&join| {
            if region.loop_transfer(join).is_some() {
                return false;
            }
            // A single live arm can own an otherwise isolated terminal
            // return. Its goto supplies the local source location.
            groups_can_own_return(self, &ordered, join, region.stop)
        });
        for (ordinal, ((target, arm), BoundArm { entry, labels })) in
            ordered.iter().zip(staged).enumerate()
        {
            let combined_null_default = Some(*target) == source_default && arm.keys == [NULL_KEY]
                && machine.supports_null_default();
            if combined_null_default {
                self.syntax(depth + 1, "case null, default:");
            } else {
                for CaseLabel { mut text, offsets } in labels {
                    text.surround("case ", ":");
                    self.push(depth + 1, text, offsets);
                }
                if Some(*target) == source_default {
                    self.syntax(depth + 1, "default:");
                }
            }
            if join == Some(*target) {
                continue;
            }
            let path = if let Some(guard) = &arm.guard {
                let Some(success) = guard.success() else {
                    self.syntax(depth + 2, "break;");
                    continue;
                };
                self.branch_arm(success, switch_region, &entry, depth + 2)?
            } else if let Some((indices, _)) = &arm.binding {
                self.pattern_arm(*target, switch_region, entry, depth + 2, indices.end)?
            } else {
                self.branch_arm(*target, switch_region, &entry, depth + 2)?
            };
            if path.exit.is_some() {
                let offsets = self.transfer_offsets(*target, &path);
                if return_join.is_some() {
                    self.push(depth + 2, Document::from("return;"), offsets);
                } else {
                    let needs_break = ordinal + 1 != ordered.len();
                    live.push((path, needs_break, offsets));
                }
            }
        }
        self.syntax(depth, "}");
        if let Some(join) = return_join {
            self.emitted[join] = true;
            return Ok(Some(None));
        }
        if join.is_some() && join == source_default {
            // A dispatch directly to the continuation has no arm body. Its
            // unchanged state still participates in the stack/local join.
            live.push((super::Arm {
                exit: Some(machine.clone()), offsets: Vec::new(),
                start: self.lines.len() - 1, end: self.lines.len() - 1,
            }, false, Vec::new()));
        }
        if live.is_empty() {
            return Ok(Some(None));
        }
        let join = join.expect("pattern switch normal arm reaches its join");
        let exits: Vec<_> = live.iter().map(|(arm, _, _)| arm).collect();
        let (declarations, assignments) = self.merge_arms(machine, join, &exits)?;
        for ((arm, needs_break, mut offsets), assignments) in
            live.into_iter().zip(assignments).rev()
        {
            let mut statements: Vec<_> = assignments
                .into_iter()
                .map(|text| Line::new(depth + 2, text, mem::take(&mut offsets)))
                .collect();
            if needs_break {
                statements.push(Line::new(depth + 2, "break;", mem::take(&mut offsets)));
            } else {
                pending.append(&mut offsets);
            }
            self.lines.splice(arm.end..arm.end, statements);
        }
        self.lines.splice(
            start..start,
            declarations
                .into_iter()
                .map(|text| Line::new(depth, text, Vec::new())),
        );
        Ok(Some(Some(join)))
    }

    fn mark_pattern_dispatch(
        &mut self,
        dispatch: usize,
        arms: &[(usize, Arm)],
    ) -> Result<(), StructureError> {
        self.emitted[dispatch] = true;
        for guard in arms.iter().filter_map(|(_, arm)| arm.guard.as_ref()) {
            for owned in guard.blocks() {
                if mem::replace(&mut self.emitted[owned], true) {
                    return Err(self.unstructured(owned));
                }
            }
        }
        Ok(())
    }

    fn transfer_offsets(&self, target: usize, path: &super::Arm<'_, '_>) -> Vec<u32> {
        if !path.offsets.is_empty() {
            return path.offsets.clone();
        }
        let range = self.graph.blocks[target].instructions.clone();
        self.instructions
            .get(range.end - 1)
            .filter(|op| matches!(op.opcode, 0xa7 | 0xc8))
            .map(|op| vec![op.offset])
            .unwrap_or_default()
    }

    fn pattern_arm<'a, 'c>(
        &mut self,
        block: usize,
        region: Region<'_, 'a, 'c>,
        mut entry: Machine<'a, 'c>,
        depth: usize,
        start: usize,
    ) -> Result<super::Arm<'a, 'c>, StructureError> {
        if !self.layout.inside(block, region)
            || self.emitted[block]
            || self.layout.loops[block].is_some()
            || self
                .exceptions
                .at_start(region.exception_arm, block)
                .is_some()
        {
            return Err(self.unstructured(block));
        }
        self.emitted[block] = true;
        let start_line = self.lines.len();
        let end = self.graph.blocks[block].instructions.end;
        let super::Tail {
            effect,
            mut offsets,
            ..
        } = self.lift_range(block, start..end, &mut entry, region, depth, Vec::new())?;
        let reaches = match effect {
            Effect::None | Effect::Jump(_) => {
                let next = self.single_successor(block)?;
                self.region_with_offsets(next, region, &mut entry, depth, &mut offsets)?
            }
            Effect::Return(value) => {
                let text = value.map_or_else(
                    || Document::from("return;"),
                    |value| super::surrounded(value, "return ", ";"),
                );
                self.push(depth, text, mem::take(&mut offsets));
                false
            }
            Effect::Throw(value) => {
                self.push(
                    depth,
                    super::surrounded(value, "throw ", ";"),
                    mem::take(&mut offsets),
                );
                false
            }
            _ => return Err(self.unstructured(block)),
        };
        Ok(super::Arm {
            exit: reaches.then_some(entry),
            offsets,
            start: start_line,
            end: self.lines.len(),
        })
    }
}

fn groups_can_own_return(
    emitter: &Emitter<'_>,
    groups: &[(usize, Arm)],
    join: usize,
    enclosing_stop: Option<usize>,
) -> bool {
    let join_block = &emitter.graph.blocks[join];
    join_block.predecessors.len() == 1
        && enclosing_stop != Some(join)
        && !emitter.emitted[join]
        && join_block.exception_predecessors.is_empty()
        && join_block.exception_successors.is_empty()
        && matches!(&emitter.instructions[join_block.instructions.clone()], [op] if op.opcode == 0xb1)
        && groups
            .iter()
            .any(|(target, _)| *target == join_block.predecessors[0])
}

#[cfg(test)]
mod tests {
    use crate::{ClassGroup, Options, bytecode::decode, classfile::ClassFile};

    use super::*;

    const CLASS: &[u8] = b"\xca\xfe\xba\xbe\0\0\0\x3d\0\x05\
        \x01\0\x01T\x07\0\x01\x01\0\x10java/lang/Object\x07\0\x03\
        \0\x21\0\x02\0\x04\0\0\0\0\0\0\0\0";

    const JAVA17_NULL_TYPE: &[u8] =
        include_bytes!("../../tests/smoke/java17preview/TestSwitchPatternMatchingWithNull.class");
    const JAVA17_INTEGER_SWITCH: &[u8] =
        include_bytes!("../../tests/smoke/java17preview/TestSwitchPatternMatching18.class");
    const JAVA17_STRING_SWITCH: &[u8] =
        include_bytes!("../../tests/smoke/java17preview/TestSwitchPatternMatching21.class");
    const ENUM_SWITCH_CLASS: &str = "pkg/TestSwitchPatternMatching19";
    const JAVA17_ENUM_SWITCH: [&[u8]; 8] = [
        include_bytes!("../../tests/smoke/java17preview/TestSwitchPatternMatching19.class"),
        include_bytes!("../../tests/smoke/java17preview/TestSwitchPatternMatching19$XXX.class"),
        include_bytes!("../../tests/smoke/java17preview/TestSwitchPatternMatching19$A.class"),
        include_bytes!("../../tests/smoke/java17preview/TestSwitchPatternMatching19$B.class"),
        include_bytes!("../../tests/smoke/java17preview/TestSwitchPatternMatching19$C.class"),
        include_bytes!("../../tests/smoke/java17preview/TestSwitchPatternMatching19$D.class"),
        include_bytes!("../../tests/smoke/java17preview/TestSwitchPatternMatching19$E.class"),
        include_bytes!("../../tests/smoke/java17preview/TestSwitchPatternMatching19$F.class"),
    ];

    #[test]
    fn preview_enum_switch_preserves_constants_guards_and_null_routing() {
        let group = ClassGroup::new(JAVA17_ENUM_SWITCH).unwrap();
        let source = group.decompile(ENUM_SWITCH_CLASS, &Options::default()).unwrap().text;
        let (first, rest) = source.split_once("void test2(").unwrap();
        let second = rest.split_once("enum XXX").unwrap().0;
        let ordered = |method: &str, labels: &[&str]| {
            let mut remaining = method;
            for label in labels {
                remaining = remaining.split_once(label).unwrap_or_else(|| panic!("{label}: {method}")).1;
            }
        };
        ordered(first, &[
            "switch (s)", "case X1:", "A a && (a !=", "B b && (", "instanceof ",
            "D d && (d == d)", "E e && (false)", "F f:", "println(\"f\")",
        ]);
        assert!(!first.contains("default:") && !first.contains("case null"), "{first}");
        ordered(second, &[
            "switch (s)", "case X1:", "case X2, null:", "println(\"maybe x2?\")",
            "F f && (Math.random() > 0.0)", "println(\"just making sure!\")",
            "default:", "println(\"default\")",
        ]);
        assert!(!source.contains("enumSwitch") && !source.contains("while ("), "{source}");
    }

    #[test]
    fn preview_enum_switch_requires_its_own_enum_class_and_names() {
        let bytes = JAVA17_ENUM_SWITCH[0];
        let class = ClassFile::parse(bytes).unwrap();
        let bootstraps = class.bootstrap_methods().unwrap();
        let blob = crate::classfile::find_attribute(&class.attributes, &class.pool, "BootstrapMethods")
            .unwrap().unwrap();
        let enum_class = bootstraps[0].arguments[1];
        assert_eq!(class.pool.class_name(enum_class).unwrap(), "pkg/TestSwitchPatternMatching19$XXX");
        let arg = blob.as_ptr() as usize - bytes.as_ptr() as usize + 8;
        let mut wrong_class = bytes.to_vec();
        assert_eq!(&wrong_class[arg..arg + 2], &enum_class.to_be_bytes());
        wrong_class[arg..arg + 2].copy_from_slice(&class.this_class.to_be_bytes());
        reject_enum_switch(&wrong_class, "test");

        let Constant::String(name) = *class.pool.get(bootstraps[1].arguments[1]).unwrap() else { panic!() };
        let name = class.pool.utf8(name).unwrap();
        assert_eq!(name, "X2");
        let mut wrong_name = bytes.to_vec();
        wrong_name[name.as_ptr() as usize - bytes.as_ptr() as usize] = b'Y';
        reject_enum_switch(&wrong_name, "test2");
    }

    #[test]
    fn preview_enum_switch_requires_a_compatible_binding_and_exact_guard_restart() {
        let bytes = JAVA17_ENUM_SWITCH[0];
        let descriptor = b"Lpkg/TestSwitchPatternMatching19$A;";
        let at = bytes.windows(descriptor.len()).position(|part| part == descriptor).unwrap();
        let mut wrong_binding = bytes.to_vec();
        wrong_binding[at + descriptor.len() - 2] = b'Z';
        reject_enum_switch(&wrong_binding, "test");

        let class = ClassFile::parse(bytes).unwrap();
        let method = class.methods.iter()
            .find(|method| class.pool.utf8(method.name_index).unwrap() == "test2").unwrap();
        let code = method.code(&class.pool).unwrap().unwrap();
        let at = code.bytes.as_ptr() as usize - bytes.as_ptr() as usize + 72;
        let mut wrong_retry = bytes.to_vec();
        assert_eq!(wrong_retry[at], 0x06); // iconst_3: retry after bootstrap label 2
        wrong_retry[at] = 0x05; // iconst_2: retries the same label
        reject_enum_switch(&wrong_retry, "test2");
    }

    fn reject_enum_switch(bytes: &[u8], expected_method: &str) {
        let mut tree = JAVA17_ENUM_SWITCH;
        tree[0] = bytes;
        let group = ClassGroup::new(tree).unwrap();
        let result = group.decompile(ENUM_SWITCH_CLASS, &Options::default());
        assert!(matches!(&result, Err(crate::DecompileError::Method { name, .. }) if name == expected_method),
            "{result:?}");
    }

    fn instructions(prefix: &[u8]) -> Vec<Instruction> {
        let mut instructions = decode(prefix).unwrap();
        let offset = prefix.len() as u32;
        instructions.extend([
            Instruction {
                offset,
                opcode: 0xba,
                operand: Operand::Constant(1),
                len: 5,
            },
            Instruction {
                offset: offset + 5,
                opcode: 0xab,
                operand: Operand::Switch {
                    default: offset + 16,
                    cases: Vec::new(),
                },
                len: 11,
            },
        ]);
        instructions
    }

    #[test]
    fn accepts_zero_restart_and_the_same_selector_alias() {
        let class = ClassFile::parse(CLASS).unwrap();
        for head in [
            [0x2a, 0x4d, 0x03, 0x3e, 0x2c, 0x1d].as_slice(),
            &[0x2a, 0x4d, 0x2c, 0x03],
        ] {
            let instructions = instructions(head);
            let shape = Head::recognize(&instructions, 0..instructions.len(), &class.pool).unwrap();
            assert_eq!(shape.setup, 1);
            assert_eq!(shape.alias, 2);
        }
    }

    #[test]
    fn rejects_nonzero_restart_or_a_different_alias() {
        let class = ClassFile::parse(CLASS).unwrap();
        for head in [
            [0x2a, 0x4d, 0x04, 0x3e, 0x2c, 0x1d],
            [0x2a, 0x4d, 0x03, 0x3e, 0x2b, 0x1d],
            [0x2a, 0x4d, 0x03, 0x3e, 0x2c, 0x1c],
        ] {
            let instructions = instructions(&head);
            assert!(Head::recognize(&instructions, 0..instructions.len(), &class.pool).is_none());
        }
    }

    #[test]
    fn proof_accounts_for_category_two_local_overlap() {
        let code = decode(&[0x1f, 0x41, 0x84, 3, 1]).unwrap();
        assert!(touches_slot(&code[0], 2));
        assert!(touches_slot(&code[1], 3));
        assert!(touches_slot(&code[2], 3));
        assert!(!touches_slot(&code[2], 4));
    }

    #[test]
    fn javac_17_combined_null_label_binds_the_original_nullable_value() {
        let group = ClassGroup::new([JAVA17_NULL_TYPE]).unwrap();
        let source = group.decompile("pkg/TestSwitchPatternMatchingWithNull", &Options::default()).unwrap().text;
        assert_eq!(source.matches("case null, Integer i").count(), 2, "{source}");
        assert_eq!(
            source.matches("System.out.println(i);").count()
                + source.matches("System.out.println((Object)i);").count(),
            2,
            "{source}",
        );
        assert!(!source.contains("requireNonNull"), "{source}");
    }

    #[test]
    fn final_java_does_not_emit_a_combined_null_and_binding_label() {
        let mut class = JAVA17_NULL_TYPE.to_vec();
        class[4..8].copy_from_slice(&[0, 0, 0, 65]);
        let group = ClassGroup::new([class.as_slice()]).unwrap();
        let result = group.decompile("pkg/TestSwitchPatternMatchingWithNull", &Options::default());
        assert!(matches!(&result,
            Err(crate::DecompileError::Method { name, source, .. }) if name == "test"
                && matches!(source.downcast_ref::<StructureError>(),
                    Some(StructureError::Lift(crate::lift::LiftError::Unsupported { opcode: 0xba, .. })))
        ), "{result:?}");
    }

    #[test]
    fn preview_integer_switch_keeps_generic_binding_and_bootstrap_priority() {
        let source = crate::decompile(JAVA17_INTEGER_SWITCH, &Options::default()).unwrap().text;
        assert_eq!(source.matches("switch (o)").count(), 3, "{source}");
        assert!(source.contains("case Comparable<Integer> ") && source.contains(".compareTo("), "{source}");
        let test2 = source.split_once("void test2(").unwrap().1.split_once("void test3(").unwrap().0;
        let test3 = source.split_once("void test3(").unwrap().1;
        let ordinal = |method: &str, label: &str| method.find(label).unwrap_or_else(|| panic!("{label}: {method}"));
        assert!(ordinal(test2, "case 16, null:") < ordinal(test2, "case Integer "));
        assert!(ordinal(test3, "case 42:") < ordinal(test3, "case Integer "));
        assert!(ordinal(test3, "case Integer ") < ordinal(test3, "case 16, null:"));
    }

    #[test]
    fn preview_string_switch_recovers_two_retries_and_the_nullable_total_binding() {
        let source = crate::decompile(JAVA17_STRING_SWITCH, &Options::default()).unwrap().text;
        assert_eq!(source.matches("switch (it)").count(), 3, "{source}");
        let (_, rest) = source.split_once("void test2(").unwrap();
        let (total, explicit_null) = rest.split_once("void test3(").unwrap();
        let guards: Vec<_> = total.match_indices("Math.random()").map(|(offset, _)| offset).collect();
        assert_eq!(guards.len(), 2, "{total}");
        let terminal = total.lines().find(|line| line.contains("case String ") && !line.contains(" && "))
            .unwrap_or_else(|| panic!("{total}"));
        assert!(guards[1] < total.find(terminal).unwrap(), "{total}");
        assert!(!total.contains("default:") && !total.contains("case null"), "{total}");
        assert!(explicit_null.contains("case \"\", null:"), "{explicit_null}");
    }

    #[test]
    fn preview_total_binding_does_not_invent_a_selector_cast_or_redirect_null() {
        let parsed = ClassFile::parse(JAVA17_STRING_SWITCH).unwrap();
        let test2 = parsed.methods.iter().find(|method| parsed.pool.utf8(method.name_index).unwrap() == "test2").unwrap();
        let code = test2.code(&parsed.pool).unwrap().unwrap();
        let base = code.bytes.as_ptr() as usize - JAVA17_STRING_SWITCH.as_ptr() as usize;
        let table = decode(code.bytes).unwrap().into_iter().find(|op| op.opcode == 0xaa).unwrap();
        let Operand::Switch { cases, .. } = table.operand else { unreachable!() };
        assert_eq!(cases[0].0, -1);
        assert_eq!(cases[1].0, 0);

        let mut wrong_null = JAVA17_STRING_SWITCH.to_vec();
        let first_case = base + ((table.offset as usize + 4) & !3) + 12;
        let wrong_target = cases[1].1 as i32 - table.offset as i32;
        wrong_null[first_case..first_case + 4].copy_from_slice(&wrong_target.to_be_bytes());
        let mut wrong_type = JAVA17_STRING_SWITCH.to_vec();
        assert_eq!(wrong_type[base], 0x2b); // aload_1 (the String parameter)
        wrong_type[base] = 0x2a; // aload_0 (this)
        for bytes in [wrong_null, wrong_type] {
            let result = crate::decompile(&bytes, &Options::default());
            assert!(matches!(result, Err(crate::DecompileError::Method { name, .. }) if name == "test2"));
        }
    }

    #[test]
    fn preview_broad_binding_requires_the_proven_generic_supertype() {
        let signature = b"Ljava/lang/Comparable<Ljava/lang/Integer;>;";
        let argument = JAVA17_INTEGER_SWITCH.windows(signature.len()).position(|bytes| bytes == signature).unwrap()
            + b"Ljava/lang/Comparable<Ljava/lang/".len();
        let mut bytes = JAVA17_INTEGER_SWITCH.to_vec();
        bytes[argument..argument + 7].copy_from_slice(b"Boolean");
        let result = crate::decompile(&bytes, &Options::default());
        assert!(matches!(result, Err(crate::DecompileError::Method { name, .. }) if name == "test"));
    }
}
