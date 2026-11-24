// Copyright 2000-2024 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use std::{
    collections::{BTreeMap, BTreeSet},
    mem,
    ops::Range,
};

use crate::{
    bytecode::{Instruction, Operand},
    classfile::{Constant, ConstantPool},
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

struct Head {
    /// The suffix replaced by the source switch, excluding selector evaluation.
    setup: usize,
    restart: u16,
    restart_store: Option<usize>,
    alias_store: usize,
    alias: u16,
    null_check: bool,
}

impl Head {
    fn recognize(
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

fn push_zero(op: &Instruction) -> bool {
    op.opcode == 0x03
        || matches!(
            (op.opcode, &op.operand),
            (0x10 | 0x11, Operand::Immediate(0))
        )
}

fn local(op: &Instruction, store: bool, reference: bool) -> Option<u16> {
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
    guard: Option<guards::Guard>,
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
        let mut constants = BTreeSet::new();
        if dispatch.labels.iter().any(|label| matches!(label, PatternLabel::Constant(text) if !constants.insert(text))) {
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
                NULL_KEY => null_target = Some(target),
                k if k >= 0 && (k as usize) < by_key.len() => by_key[k as usize] = Some(target),
                k if k == by_key.len() as i32 && target == default => {}
                _ if target == default => {} // tableswitch padding
                _ => return Ok(None),
            }
        }
        for (key, target) in by_key.into_iter().enumerate() {
            let Some(target) = target.filter(|&target| target != default) else {
                return Ok(None);
            };
            groups.entry(target).or_default().keys.push(key as i32);
        }
        if !head.null_check {
            // Even when the integer switch omits -1, the bootstrap gives null
            // to its default arm, unlike a Java switch without a null label.
            let target = null_target.unwrap_or(default);
            groups.entry(target).or_default().keys.push(NULL_KEY);
        } else if null_target.is_some_and(|target| target != default) {
            return Ok(None);
        }

        let mut alias_uses = BTreeSet::from([indy - 2, head.alias_store]);
        let targets: BTreeSet<_> = groups.keys().copied().collect();
        let mut pattern_types = Vec::new();
        for (&target, arm) in &mut groups {
            let cfg = &self.graph.blocks[target];
            if !cfg.exception_predecessors.is_empty()
                || !cfg.predecessors.contains(&dispatch_block)
                || target != default && cfg.predecessors != [dispatch_block]
            {
                return Ok(None);
            }
            let [key] = arm.keys.as_slice() else {
                if arm.keys.iter().any(|&key| {
                    key != NULL_KEY
                        && matches!(dispatch.labels[key as usize], PatternLabel::Type(_))
                }) {
                    return Ok(None);
                }
                continue;
            };
            if *key == NULL_KEY {
                continue;
            }
            let PatternLabel::Type(ty) = &dispatch.labels[*key as usize] else {
                continue;
            };
            let mut body_start = cfg.instructions.start;
            let body = &self.instructions[cfg.instructions.clone()];
            if body
                .first()
                .is_some_and(|op| local(op, false, true) == Some(head.alias))
            {
                let (width, slot) = match body {
                    [_, cast, store, ..] if cast.opcode == 0xc0 => {
                        let Operand::Constant(index) = cast.operand else {
                            return Ok(None);
                        };
                        if machine.pattern_class(index)? != *ty {
                            return Ok(None);
                        }
                        let Some(slot) = local(store, true, true) else {
                            return Ok(None);
                        };
                        (3, slot)
                    }
                    _ => return Ok(None),
                };
                if slot == head.alias || head.restart_store.is_some() && slot == head.restart {
                    return Ok(None);
                }
                alias_uses.insert(cfg.instructions.start);
                arm.binding = Some((cfg.instructions.start..cfg.instructions.start + width, slot));
                body_start += width;
            }
            if let Some(proof) = &restart {
                let Some(guard) = proof.arm(self, target, body_start, *key, &targets) else {
                    return Ok(None);
                };
                arm.guard = guard;
            }
            // Only a genuinely unconditional pattern can dominate later
            // labels or conflict with default.
            if arm.guard.is_none() {
                if machine.pattern_covers(ty, &dispatch.selector) {
                    return Ok(None);
                }
                pattern_types.push((*key, ty));
            }
        }
        for arm in groups.values() {
            for &key in &arm.keys {
                if key != NULL_KEY
                    && let PatternLabel::Type(ty) = &dispatch.labels[key as usize]
                    && pattern_types.iter().any(|&(earlier, prior)| earlier < key && machine.pattern_covers(prior, ty))
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
                        && !restart.as_ref().is_some_and(|proof| proof.restart_store(self, index))
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
                groups.iter().map(|(&target, arm)| (arm.guard.as_ref().map_or(target, |guard| guard.success), None)),
            ))
            .or(region.stop);
        if groups.keys().any(|&target| Some(target) == join && target != default)
            || join != Some(default) && self.graph.blocks[default].predecessors != [dispatch_block]
        {
            return Ok(None);
        }
        let switch_region = within.switch_body(join);
        let mut ordered: Vec<_> = groups.into_iter().collect();
        // Preserve the bootstrap matching order even if the bytecode lays
        // the switch blocks out differently. Null never competes with a type.
        ordered.sort_by_key(|(target, arm)| {
            if *target == default {
                (2, 0)
            } else if arm.keys == [NULL_KEY] {
                (0, 0)
            } else {
                (1, arm.keys.first().copied().unwrap_or_default())
            }
        });

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
        let (selector, control) = machine.take_pattern_selector(
            &self.instructions[head.setup],
            &dispatch.selector,
            dispatch.labels.iter().any(|label| matches!(label, PatternLabel::Type(_))),
            switch.offset + switch.len - 1,
        )?;
        let guard_keyword = machine.pattern_guard_keyword().ok_or_else(|| self.unstructured(block))?;
        let mut staged = Vec::with_capacity(ordered.len());
        let names = machine.local_name_checkpoint();
        let anonymous = machine.switch_anonymous_checkpoint();
        let baseline = machine.switch_arm_entry(&control)?;
        let trial = (|| {
            for (target, arm) in &ordered {
                let mut entry = baseline.clone();
                let mut binding_offsets = Vec::new();
                let mut labels = Vec::with_capacity(arm.keys.len());
                if let Some((indices, _)) = &arm.binding {
                    let store = &self.instructions[indices.end - 1];
                    binding_offsets.extend(store.offset..store.offset + store.len);
                }
                for &key in &arm.keys {
                    let mut label: Document = if key == NULL_KEY {
                        "null".into()
                    } else {
                        match &dispatch.labels[key as usize] {
                            PatternLabel::Constant(text) => text.as_str().into(),
                            PatternLabel::Type(ty) => entry.pattern_binding(
                                ty,
                                arm.binding.as_ref().map(|(indices, slot)| {
                                    (&self.instructions[indices.end - 1], Some(&self.instructions[indices.start + 1]), *slot)
                                }),
                                self.offset(*target),
                            )?,
                        }
                    };
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
        machine.commit_switch_dynamic_helpers(&baseline);
        offsets.extend(switch.offset..switch.offset + switch.len);
        if restart.is_none()
            && let Some(join) = join
            && self.try_pattern_switch_value(
                dispatch_block, region, machine, depth, &selector, &ordered, &staged, default, join, &control,
            )
        {
            *pending = offsets;
            return Ok(Some(Some(join)));
        }
        if !machine.stack_is_empty() {
            return Err(self.unstructured(block));
        }
        self.emitted[dispatch_block] = true;
        for arm in ordered.iter().filter_map(|(_, arm)| arm.guard.as_ref()) {
            for owned in arm.blocks() {
                if mem::replace(&mut self.emitted[owned], true) {
                    return Err(self.unstructured(owned));
                }
            }
        }
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
            let combined_null_default = *target == default && arm.keys == [NULL_KEY]
                && machine.supports_null_default();
            if combined_null_default {
                self.syntax(depth + 1, "case null, default:");
            } else {
                for CaseLabel { mut text, offsets } in labels {
                    text.surround("case ", ":");
                    self.push(depth + 1, text, offsets);
                }
                if *target == default {
                    self.syntax(depth + 1, "default:");
                }
            }
            if join == Some(*target) {
                continue;
            }
            let path = if let Some(guard) = &arm.guard {
                self.branch_arm(guard.success, switch_region, &entry, depth + 2)?
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
        if join == Some(default) {
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
    use crate::{bytecode::decode, classfile::ClassFile};

    use super::*;

    const CLASS: &[u8] = b"\xca\xfe\xba\xbe\0\0\0\x3d\0\x05\
        \x01\0\x01T\x07\0\x01\x01\0\x10java/lang/Object\x07\0\x03\
        \0\x21\0\x02\0\x04\0\0\0\0\0\0\0\0";

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
}
