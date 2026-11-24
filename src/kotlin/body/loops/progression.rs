// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.

use crate::classfile::Constant;

use super::{
    Direction, Element, Expr, Instruction, KotlinError, Literal, Operand, Primitive, Shape, Source,
    Template, backward, branch_to, integer, is_increment, local_load, local_store, same, slot_read,
};

const PROGRESSION: &str = "kotlin/ranges/IntProgression";
const RANGES: &str = "kotlin/ranges/RangesKt";

pub(super) fn recognize<'a>(shape: &Shape<'_, 'a, '_>) -> Result<Option<Template<'a>>, KotlinError> {
    if let Some(template) = shape.materialized()? { return Ok(Some(template)); }
    shape.inlined()
}

impl<'class> Shape<'_, 'class, '_> {
    /// Inlined constant or runtime step. Prove the same first, step and end
    /// operands feed progression rounding, entry check, equality latch and
    /// signed update. Kotlin exits at the last element before an overflow.
    fn inlined(&self) -> Result<Option<Template<'class>>, KotlinError> {
        let (back, exit) = self.final_indices();
        let mut first_index = 0;
        let mut source_step = None;
        let mut negative_step_slot = None;
        if let Some(step) = self.step_check()? {
            source_step = Some(step);
            first_index = 8;
            if let Some([load, neg, store]) = self.instructions.get(first_index..first_index + 3)
                && same(load, step) && neg.opcode == 0x74
                && let Some((0x36, slot)) = local_store(store)
                && slot >= self.locals.next_slot()
            {
                negative_step_slot = Some(slot);
                first_index += 3;
            }
        }
        let [first, save, duplicate, last, step, rounded, save_last, left, right, guard, ..] =
            &self.instructions[first_index..] else { return Ok(None); };
        let Some((0x36, slot)) = local_store(save) else { return Ok(None); };
        let Some((0x36, last_slot)) = local_store(save_last) else { return Ok(None); };
        let body_start = first_index + 10;
        if body_start >= back || !same(first, duplicate) || slot == last_slot
            || slot.min(last_slot) < self.locals.next_slot()
            || negative_step_slot.is_some_and(|signed| signed == slot || signed == last_slot)
            || !self.bytecode.reference(rounded, 0xb8)?.is_some_and(|target|
                target == ("kotlin/internal/ProgressionUtilKt", "getProgressionLastElement", "(III)I"))
            || !branch_to(guard, 0xa3, &self.instructions[exit])
            || !backward(&self.instructions[back], &self.instructions[body_start])
        { return Ok(None); }
        let Some(first) = self.atom(first, 0x15)? else { return Ok(None); };
        let Some(last) = self.atom(last, 0x15)? else { return Ok(None); };
        let (direction, magnitude, update_start) = if let Some(source_step) = source_step {
            let (direction, signed_slot) = if let Some(signed) = negative_step_slot {
                if !slot_read(step, signed) { return Ok(None); }
                (Direction::Descend, signed)
            } else {
                if !same(step, source_step) { return Ok(None); }
                let Some((0x15, slot)) = local_load(step) else { return Ok(None); };
                (Direction::Ascend, slot)
            };
            if back < body_start + 7 || !self.variable_update(back, slot, signed_slot) {
                return Ok(None);
            }
            let Some(magnitude) = self.atom(source_step, 0x15)? else { return Ok(None); };
            (direction, magnitude, back - 4)
        } else {
            let Some(value) = self.atom(step, 0x15)? else { return Ok(None); };
            let Some(signed) = integer(&value).filter(|step| *step != 0) else { return Ok(None); };
            let Ok(amount) = i16::try_from(signed) else { return Ok(None); };
            if back < body_start + 4 || !is_increment(&self.instructions[back - 1], slot, amount) { return Ok(None); }
            let direction = if signed > 0 { Direction::Ascend } else { Direction::Descend };
            (direction, Expr::literal(Literal::Int(signed.abs())), back - 1)
        };
        let entry = if direction == Direction::Ascend { (slot, last_slot) } else { (last_slot, slot) };
        if !slot_read(left, entry.0) || !slot_read(right, entry.1) || !self.equal_latch(update_start, slot, last_slot, exit) {
            return Ok(None);
        }
        Ok(Some(Template {
            source: Source::Range { first, last, step: Some(magnitude), direction },
            slot, element: Element::Primitive(Primitive::Int), scope_start: first_index + 2,
            scope_end: exit, first_free: slot.max(last_slot).max(negative_step_slot.unwrap_or(0)).saturating_add(1),
            body: body_start..update_start - 3,
        }))
    }

    /// `until(...).step(...)` evaluates a progression once and copies its
    /// first, last and signed step. The two entry guards distinguish empty
    /// progressions from a valid singleton before entering the common loop.
    fn materialized(&self) -> Result<Option<Template<'class>>, KotlinError> {
        let [first, last, range, cast, step, invoke_step, save, get_first, call_first, save_first,
            get_last, call_last, save_last, get_step, call_step, save_step,
            pos, if_pos, first_pos, last_pos, enter, neg, if_neg, last_neg, first_neg, leave, ..] = self.instructions
        else { return Ok(None); };
        let direction = match self.bytecode.reference(range, 0xb8)? {
            Some((RANGES, "until", "(II)Lkotlin/ranges/IntRange;")) => Direction::Until,
            Some((RANGES, "downTo", "(II)Lkotlin/ranges/IntProgression;")) => Direction::Descend,
            _ => return Ok(None),
        };
        if !self.class_operation(cast, 0xc0, PROGRESSION)? || self.bytecode.reference(invoke_step, 0xb8)?
            != Some((RANGES, "step", "(Lkotlin/ranges/IntProgression;I)Lkotlin/ranges/IntProgression;"))
        { return Ok(None); }
        let Some((0x3a, range_slot)) = local_store(save) else { return Ok(None); };
        let Some((0x36, slot)) = local_store(save_first) else { return Ok(None); };
        let Some((0x36, last_slot)) = local_store(save_last) else { return Ok(None); };
        let Some((0x36, step_slot)) = local_store(save_step) else { return Ok(None); };
        let slots = [range_slot, slot, last_slot, step_slot];
        if slots.iter().enumerate().any(|(i, slot)| *slot < self.locals.next_slot() || slots[..i].contains(slot)) { return Ok(None); }
        for (get, invoke, name) in [(get_first, call_first, "getFirst"), (get_last, call_last, "getLast"), (get_step, call_step, "getStep")] {
            if local_load(get) != Some((0x19, range_slot)) || self.bytecode.reference(invoke, 0xb6)? != Some((PROGRESSION, name, "()I")) {
                return Ok(None);
            }
        }
        let (back, exit) = self.final_indices();
        let body_start = 26;
        if back < body_start + 7 || !slot_read(pos, step_slot) || !branch_to(if_pos, 0x9e, neg)
            || !slot_read(first_pos, slot) || !slot_read(last_pos, last_slot)
            || !branch_to(enter, 0xa4, &self.instructions[body_start])
            || !slot_read(neg, step_slot) || !branch_to(if_neg, 0x9c, &self.instructions[exit])
            || !slot_read(last_neg, last_slot) || !slot_read(first_neg, slot) || !branch_to(leave, 0xa3, &self.instructions[exit])
            || !backward(&self.instructions[back], &self.instructions[body_start]) || !self.variable_update(back, slot, step_slot)
            || !self.equal_latch(back - 4, slot, last_slot, exit)
        { return Ok(None); }
        let (Some(first), Some(last), Some(step)) = (self.atom(first, 0x15)?, self.atom(last, 0x15)?, self.atom(step, 0x15)?) else { return Ok(None); };
        Ok(Some(Template {
            source: Source::Range { first, last, step: Some(step), direction },
            slot, element: Element::Primitive(Primitive::Int), scope_start: 10, scope_end: exit,
            first_free: slots.into_iter().max().unwrap().saturating_add(1), body: body_start..back - 7,
        }))
    }

    fn variable_update(&self, back: usize, slot: u16, step: u16) -> bool {
        matches!(&self.instructions[back - 4..back], [read, delta, add, store]
            if slot_read(read, slot) && slot_read(delta, step) && add.opcode == 0x60 && local_store(store) == Some((0x36, slot)))
    }

    fn equal_latch(&self, update: usize, slot: u16, last: u16, exit: usize) -> bool {
        matches!(&self.instructions[update - 3..update], [read, bound, guard]
            if slot_read(read, slot) && slot_read(bound, last) && branch_to(guard, 0x9f, &self.instructions[exit]))
    }

    /// Match the compiler's validated dynamic step prelude, including the
    /// exception class, bootstrap target and string recipe. Unknown error
    /// paths cannot safely be replaced by `step`.
    fn step_check(&self) -> Result<Option<&Instruction>, KotlinError> {
        let [load, guard, new, dup, duplicate, concat, init, throw, next, ..] = self.instructions else { return Ok(None); };
        if !matches!(local_load(load), Some((0x15, slot)) if self.locals.parameter(slot, 0x15).is_some())
            || !branch_to(guard, 0x9d, next) || !self.class_operation(new, 0xbb, "java/lang/IllegalArgumentException")?
            || dup.opcode != 0x59 || !same(duplicate, load) || !matches!(concat.opcode, 0xba) || throw.opcode != 0xbf
            || self.bytecode.reference(init, 0xb7)? != Some(("java/lang/IllegalArgumentException", "<init>", "(Ljava/lang/String;)V"))
        { return Ok(None); }
        let Operand::Constant(index) = concat.operand else { return Ok(None); };
        let pool = &self.bytecode.class.pool;
        let Constant::InvokeDynamic { bootstrap_index, name_and_type_index } = *pool.get(index)? else { return Ok(None); };
        if pool.name_and_type(name_and_type_index)? != ("makeConcatWithConstants", "(I)Ljava/lang/String;") { return Ok(None); }
        let bootstraps = self.bytecode.class.bootstrap_methods()?;
        let Some(bootstrap) = bootstraps.get(usize::from(bootstrap_index)) else { return Ok(None); };
        let Constant::MethodHandle { reference_kind: 6, reference_index } = *pool.get(bootstrap.method_ref)? else { return Ok(None); };
        if pool.member_ref(reference_index)? != ("java/lang/invoke/StringConcatFactory", "makeConcatWithConstants",
            "(Ljava/lang/invoke/MethodHandles$Lookup;Ljava/lang/String;Ljava/lang/invoke/MethodType;Ljava/lang/String;[Ljava/lang/Object;)Ljava/lang/invoke/CallSite;")
        { return Ok(None); }
        let [recipe] = bootstrap.arguments.as_slice() else { return Ok(None); };
        let Constant::String(recipe) = *pool.get(*recipe)? else { return Ok(None); };
        Ok((pool.utf8(recipe)? == "Step must be positive, was: \u{1}.").then_some(load))
    }
}
