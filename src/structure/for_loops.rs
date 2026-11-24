// Based on Vineflower MergeHelper (Apache-2.0).
// Copyright 2000-2020 JetBrains s.r.o.

use std::{mem, ops::Range};

use crate::{
    bytecode::{Instruction, Operand},
    descriptor::{Primitive, Type},
    lift::{Effect, Machine},
    source_text::Document,
};

use super::{Emitter, Line, Region, While};

pub(super) struct ForLoop {
    setup: Range<usize>,
    style: Style,
    pub(super) latch: Option<usize>,
    pub(super) update: Option<usize>,
    pub(super) element: Option<Range<usize>>,
    forget: Vec<u16>,
    offsets: Vec<u32>,
    hidden_offsets: Option<[Range<u32>; 4]>,
}

enum Style {
    Counted(Document),
    Enhanced { binding: Document, holder: Document },
}

impl ForLoop {
    pub(super) fn write(
        self,
        lines: &mut Vec<Line>,
        header: usize,
        condition: Document,
        machine: &mut Machine<'_, '_>,
    ) -> usize {
        let removed = self.setup.len();
        let mut offsets = Vec::new();
        let mut text = Document::from("for (");
        match self.style {
            Style::Counted(update) => {
                let init = &mut lines[self.setup.start];
                offsets.append(&mut init.offsets);
                // `setup` identifies the lifted store instruction, not a
                // textual assignment pattern. Remove only its terminator.
                let mut init = mem::take(&mut init.text);
                let terminator = init.pop();
                debug_assert_eq!(terminator, Some(';'));
                text.append(init);
                text.push_str("; ");
                text.append(condition);
                text.push_str("; ");
                text.append(update);
            }
            Style::Enhanced { binding, holder } => {
                for line in &mut lines[self.setup.clone()] {
                    offsets.append(&mut line.offsets);
                }
                text.append(binding);
                text.push_str(" : ");
                text.append(holder);
            }
        }
        text.push_str(") {");
        let line = &mut lines[header];
        offsets.append(&mut line.offsets);
        offsets.extend(self.offsets);
        if let Some(hidden) = &self.hidden_offsets {
            offsets.retain(|offset| !hidden.iter().any(|range| range.contains(offset)));
        }
        line.text = text;
        line.offsets = offsets;
        lines.drain(self.setup);
        for slot in self.forget {
            machine.forget_binding(slot);
        }
        removed
    }
}

struct Seed {
    preheader: usize,
    latch: usize,
    handler_latch: Option<usize>,
    line: usize,
}

struct Count {
    slot: u16,
    update: usize,
    amount: i16,
    latch: Option<usize>,
    init_line: usize,
    next: Document,
}

struct Enhanced {
    setup: Range<usize>,
    element: Range<usize>,
    element_slot: u16,
    element_type: Type,
    holder: Document,
    helpers: [Option<u16>; 3],
    omitted_uses: Vec<usize>,
    hidden_offsets: Option<[Range<u32>; 4]>,
}

impl Emitter<'_> {
    pub(super) fn skips_to_counted_latch(
        &self,
        head: usize,
        arm: usize,
        region: Region<'_, '_, '_>,
    ) -> bool {
        let Some(latch) = region.counted_latch() else {
            return false;
        };
        if arm == latch || region.stop != Some(latch) || self.emitted[arm] {
            return false;
        }
        let block = &self.graph.blocks[arm];
        if block.predecessors.as_slice() != [head] || block.successors.as_slice() != [latch] {
            return false;
        }
        let Some((jump, prefix)) = self.instructions[block.instructions.clone()].split_last()
        else {
            return false;
        };
        prefix.iter().all(|op| op.opcode == 0)
            && matches!(jump.opcode, 0xa7 | 0xc8)
            && jump.operand == Operand::Branch(self.offset(latch))
    }

    /// The ordinary loop header has already been lifted and is unchanged
    /// across its test. All syntax suppression below is chosen from bytecode
    /// identities and source-map boundaries, never from rendered bindings.
    pub(super) fn prove_for_loop<'a, 'c>(
        &mut self,
        header: usize,
        test: While,
        region: Region<'_, 'a, 'c>,
        entry: &Machine<'a, 'c>,
        iteration: &mut Machine<'a, 'c>,
        head_line: usize,
        depth: usize,
    ) -> Option<ForLoop> {
        if region.exception_arm.is_some()
            || !entry.stack_is_empty()
            || !iteration.stack_is_empty()
            || !entry.same_locals(iteration)
        {
            return None;
        }
        let seed = self.for_seed(header, test.exit, head_line, depth)?;
        let count = self.counting_tail(header, &seed, entry);
        let enhanced = count
            .as_ref()
            .and_then(|count| self.array_foreach(header, test.body, &seed, count, entry, depth))
            .or_else(|| self.iterator_foreach(header, test.body, &seed, entry));
        if let Some(enhanced) = enhanced
            && entry.supports_enhanced_for()
            && self.graph.blocks[test.body].exception_successors.is_empty()
            && self.safe_for_body(
                header,
                test,
                &enhanced.helpers,
                &enhanced.omitted_uses,
                seed.handler_latch,
                false,
            )
            && !(enhanced.element_slot
                ..enhanced
                    .element_slot
                    .saturating_add(enhanced.element_type.slots()))
                .any(|slot| self.local_is_live(test.exit, slot))
            && self.graph.blocks[test.body].predecessors.as_slice() == [header]
            && !self.assertion_starts(test.body)
            && self.layout.loops[test.body].is_none()
        {
            let store = &self.instructions[enhanced.element.end - 1];
            let binding =
                iteration.bind_loop_element(store, enhanced.element_slot, enhanced.element_type)?;
            let mut forget = enhanced.helpers.into_iter().flatten().collect::<Vec<_>>();
            forget.push(enhanced.element_slot);
            let array = enhanced.helpers[1].is_some();
            let (latch, update) = match (array, count) {
                (true, Some(count)) => (count.latch, Some(count.update)),
                (false, _) => (None, None),
                _ => unreachable!("array proof requires a counting tail"),
            };
            let mut offsets =
                useful_offsets(&self.instructions[enhanced.element.clone()]).collect::<Vec<_>>();
            if let Some(update) = update {
                offsets.extend(useful_offsets(&self.instructions[update..update + 1]));
            }
            return Some(ForLoop {
                setup: enhanced.setup,
                style: Style::Enhanced {
                    binding,
                    holder: enhanced.holder,
                },
                latch,
                update,
                element: Some(enhanced.element),
                forget,
                offsets,
                hidden_offsets: enhanced.hidden_offsets,
            });
        }
        let count = count?;
        if self.local_is_live(test.exit, count.slot)
            || !self.safe_for_body(header, test, &[None; 3], &[count.update], None, true)
        {
            return None;
        }
        Some(ForLoop {
            setup: count.init_line..count.init_line + 1,
            style: Style::Counted(count.next),
            latch: count.latch,
            update: Some(count.update),
            element: None,
            forget: vec![count.slot],
            offsets: useful_offsets(&self.instructions[count.update..count.update + 1]).collect(),
            hidden_offsets: None,
        })
    }

    fn for_seed(&self, header: usize, exit: usize, line: usize, depth: usize) -> Option<Seed> {
        let node = &self.graph.blocks[header];
        let [first, second] = *node.predecessors.as_slice() else {
            return None;
        };
        let (preheader, latch) = match (self.emitted[first], self.emitted[second]) {
            (true, false) => (first, second),
            (false, true) => (second, first),
            _ => return None,
        };
        let handler_latch = if self.graph.blocks[latch].exception_predecessors.is_empty() {
            None
        } else {
            self.exceptions.handler_latch(header, exit).filter(|&handler| handler == latch)
        };
        if preheader == header
            || latch == header
            || self.graph.blocks[preheader].successors.as_slice() != [header]
            || self.graph.blocks[latch].successors.as_slice() != [header]
            || !self.layout.direct_loop_member(latch, header)
            || self.layout.loops[latch].is_some()
            || [preheader, header, latch].into_iter().any(|block| {
                !self.graph.blocks[block].exception_successors.is_empty()
                    || (Some(block) != handler_latch
                        && !self.graph.blocks[block].exception_predecessors.is_empty())
            })
        {
            return None;
        }
        if self.graph.blocks[preheader].instructions.end
            != self.graph.blocks[header].instructions.start
        {
            return None;
        }
        let line = line.checked_sub(1)?;
        let store = self.preheader_store_end(preheader)?;
        self.line_ends_at_store(line, depth, store).then_some(Seed {
            preheader,
            latch,
            handler_latch,
            line,
        })
    }

    fn earlier_local_store(&self, slot: u16, before: usize) -> bool {
        self.instructions[..before]
            .iter()
            .any(|op| match access(op) {
                Some(Access::Store(kind, write)) => {
                    write == slot
                        || matches!(kind, Kind::Long | Kind::Double)
                            && write.checked_add(1) == Some(slot)
                }
                Some(Access::Increment(write)) => write == slot,
                _ => false,
            })
    }

    fn preheader_store_end(&self, block: usize) -> Option<usize> {
        let range = &self.graph.blocks[block].instructions;
        (range.clone())
            .rev()
            .find(|&index| !matches!(self.instructions[index].opcode, 0 | 0xa7 | 0xc8))
    }

    fn line_ends_at_store(&self, line: usize, depth: usize, index: usize) -> bool {
        let op = &self.instructions[index];
        matches!(access(op), Some(Access::Store(..)))
            && self.lines.get(line).is_some_and(|line| {
                line.depth == depth
                    && line.loop_break.is_none()
                    && line.offsets.last() == Some(&(op.offset + op.len - 1))
            })
    }

    fn counting_tail(&self, header: usize, seed: &Seed, entry: &Machine<'_, '_>) -> Option<Count> {
        let range = &self.graph.blocks[seed.latch].instructions;
        let update = range.end.checked_sub(2)?;
        if update < range.start {
            return None;
        }
        let [increment, backedge] = &self.instructions[update..range.end] else {
            return None;
        };
        let Operand::Increment {
            index: slot,
            amount,
        } = increment.operand
        else {
            return None;
        };
        if amount == 0
            || !matches!(backedge.opcode, 0xa7 | 0xc8)
            || backedge.operand != Operand::Branch(self.offset(header))
        {
            return None;
        }
        let store = self.preheader_store_end(seed.preheader)?;
        if access(&self.instructions[store]) != Some(Access::Store(Kind::Int, slot))
            || !entry.loop_binding_starts_here(
                slot,
                &self.instructions[store],
                self.earlier_local_store(slot, store),
            )
        {
            return None;
        }
        let mut probe = entry.clone();
        let Effect::Statement(mut next) = probe.step(increment).ok()? else {
            return None;
        };
        if !probe.take_prelude().is_empty() {
            return None;
        }
        let terminator = next.pop();
        debug_assert_eq!(terminator, Some(';'));
        Some(Count {
            slot,
            update,
            amount,
            latch: (update == range.start).then_some(seed.latch),
            init_line: seed.line,
            next,
        })
    }

    fn array_foreach(
        &self,
        header: usize,
        body: usize,
        seed: &Seed,
        count: &Count,
        entry: &Machine<'_, '_>,
        depth: usize,
    ) -> Option<Enhanced> {
        if count.amount != 1 {
            return None;
        }
        let end = self.preheader_store_end(seed.preheader)? + 1;
        let start = end.checked_sub(7)?;
        if start < self.graph.blocks[seed.preheader].instructions.start {
            return None;
        }
        let [
            holder,
            alias_store,
            cache,
            array_length,
            bound_store,
            zero,
            index_store,
        ] = &self.instructions[start..end]
        else {
            return None;
        };
        let Access::Load(Kind::Ref, holder_slot) = access(holder)? else {
            return None;
        };
        let Access::Store(Kind::Ref, alias) = access(alias_store)? else {
            return None;
        };
        let Access::Store(Kind::Int, bound) = access(bound_store)? else {
            return None;
        };
        if access(cache) != Some(Access::Load(Kind::Ref, alias))
            || array_length.opcode != 0xbe
            || zero.opcode != 0x03
            || access(index_store) != Some(Access::Store(Kind::Int, count.slot))
            || !distinct(&[holder_slot, alias, bound, count.slot])
            || !entry.loop_binding_starts_here(
                alias,
                alias_store,
                self.earlier_local_store(alias, start + 1),
            )
            || !entry.loop_binding_starts_here(
                bound,
                bound_store,
                self.earlier_local_store(bound, start + 4),
            )
            || !self.line_ends_at_store(seed.line.checked_sub(1)?, depth, start + 4)
            || !self.line_ends_at_store(seed.line.checked_sub(2)?, depth, start + 1)
        {
            return None;
        }
        let [index, length, branch] =
            &self.instructions[self.graph.blocks[header].instructions.clone()]
        else {
            return None;
        };
        if access(index) != Some(Access::Load(Kind::Int, count.slot))
            || access(length) != Some(Access::Load(Kind::Int, bound))
            || branch.opcode != 0xa2
            || branch.operand == Operand::Branch(self.offset(body))
        {
            return None;
        }
        let body_start = self.graph.blocks[body].instructions.start;
        let [array, index, get, store, ..] =
            &self.instructions[self.graph.blocks[body].instructions.clone()]
        else {
            return None;
        };
        let Access::Store(kind, element_slot) = access(store)? else {
            return None;
        };
        let Type::Array(element) = entry.local_binding_type(holder_slot)? else {
            return None;
        };
        let holder = entry.loop_receiver(holder_slot)?;
        let (load, element_kind) = element_load(element);
        if access(array) != Some(Access::Load(Kind::Ref, alias))
            || access(index) != Some(Access::Load(Kind::Int, count.slot))
            || get.opcode != load
            || kind != element_kind
            || !distinct(&[holder_slot, alias, bound, count.slot, element_slot])
        {
            return None;
        }
        let header_start = self.graph.blocks[header].instructions.start;
        Some(Enhanced {
            setup: seed.line - 2..seed.line + 1,
            element: body_start..body_start + 4,
            element_slot,
            element_type: (**element).clone(),
            holder,
            helpers: [Some(alias), Some(bound), Some(count.slot)],
            omitted_uses: vec![
                header_start,
                header_start + 1,
                body_start,
                body_start + 1,
                count.update,
            ],
            // Source foreach owns the holder and the binding stores; it
            // does not have separate length, index, or element expressions.
            hidden_offsets: Some([
                array_length.offset..array_length.offset + array_length.len,
                zero.offset..zero.offset + zero.len,
                self.instructions[header_start].offset..branch.offset + branch.len,
                array.offset..get.offset + get.len,
            ]),
        })
    }

    fn iterator_foreach(
        &self,
        header: usize,
        body: usize,
        seed: &Seed,
        entry: &Machine<'_, '_>,
    ) -> Option<Enhanced> {
        let end = self.preheader_store_end(seed.preheader)? + 1;
        let start = end.checked_sub(3)?;
        if start < self.graph.blocks[seed.preheader].instructions.start {
            return None;
        }
        let [holder, iterator, store] = &self.instructions[start..end] else {
            return None;
        };
        let Access::Load(Kind::Ref, holder_slot) = access(holder)? else {
            return None;
        };
        let Access::Store(Kind::Ref, iterator_slot) = access(store)? else {
            return None;
        };
        let (owner, "iterator", "()Ljava/util/Iterator;") = instance_member(entry, iterator)?
        else {
            return None;
        };
        let holder_type = entry.local_binding_type(holder_slot)?;
        if holder_slot == iterator_slot
            || !entry.proves_iterable(holder_type, owner)
            || !entry.loop_binding_starts_here(
                iterator_slot,
                store,
                self.earlier_local_store(iterator_slot, start + 2),
            )
        {
            return None;
        }
        let [receiver, has_next, branch] =
            &self.instructions[self.graph.blocks[header].instructions.clone()]
        else {
            return None;
        };
        if access(receiver) != Some(Access::Load(Kind::Ref, iterator_slot))
            || instance_member(entry, has_next)? != ("java/util/Iterator", "hasNext", "()Z")
            || branch.opcode != 0x99
            || branch.operand == Operand::Branch(self.offset(body))
        {
            return None;
        }
        let body_range = self.graph.blocks[body].instructions.clone();
        let [receiver, next, tail @ ..] = &self.instructions[body_range.clone()] else {
            return None;
        };
        if access(receiver) != Some(Access::Load(Kind::Ref, iterator_slot))
            || instance_member(entry, next)?
                != ("java/util/Iterator", "next", "()Ljava/lang/Object;")
        {
            return None;
        }
        let (element_type, reference, tail) = if let [cast, tail @ ..] = tail
            && cast.opcode == 0xc0
            && let Operand::Constant(index) = cast.operand
        {
            let name = entry.constant_pool().class_name(index).ok()?;
            let reference = if name.starts_with('[') {
                Type::parse(name).ok()?
            } else {
                Type::Object(name.into())
            };
            if let Some((primitive, tail)) = unboxing(entry, name, tail) {
                (Type::Primitive(primitive), reference, tail)
            } else {
                (reference.clone(), reference, tail)
            }
        } else {
            let object = Type::Object("java/lang/Object".into());
            (object.clone(), object, tail)
        };
        let [store, rest @ ..] = tail else {
            return None;
        };
        let Access::Store(kind, element_slot) = access(store)? else {
            return None;
        };
        if kind != element_kind(&element_type)
            || !distinct(&[holder_slot, iterator_slot, element_slot])
        {
            return None;
        }
        let receiver = entry.loop_receiver(holder_slot)?;
        let mut holder = Document::new();
        if !matches!(&reference, Type::Object(name) if name == "java/lang/Object")
            && !entry.loop_receiver_has_element(holder_slot, &reference, owner)
        {
            // A local's JVM type is erased. Reconstruct the proven cast or
            // unboxing as the language's element conversion, not a cast of
            // the entire collection to an implementation type.
            let iterable = entry.render_loop_type(&Type::Object("java/lang/Iterable".into()));
            holder.push('(');
            holder.push_str(&iterable);
            holder.push('<');
            holder.push_str(&entry.render_loop_type(&reference));
            holder.push_str(">)(");
            holder.push_str(&iterable);
            holder.push_str("<?>)");
        }
        holder.append(receiver);
        Some(Enhanced {
            setup: seed.line..seed.line + 1,
            element: body_range.start..body_range.end - rest.len(),
            element_slot,
            element_type,
            holder,
            helpers: [Some(iterator_slot), None, None],
            omitted_uses: vec![
                self.graph.blocks[header].instructions.start,
                body_range.start,
            ],
            hidden_offsets: None,
        })
    }

    fn safe_for_body(
        &mut self,
        header: usize,
        test: While,
        helpers: &[Option<u16>; 3],
        omitted: &[usize],
        handler_latch: Option<usize>,
        allow_finally: bool,
    ) -> bool {
        let graph = self.graph;
        let instructions = self.instructions;
        if helpers
            .iter()
            .flatten()
            .any(|&slot| self.local_is_live(test.exit, slot))
        {
            return false;
        }
        let mut seen = vec![false; graph.blocks.len()];
        let mut pending = vec![header];
        let mut has_body = false;
        let mut live = std::collections::BTreeMap::new();
        while let Some(block) = pending.pop() {
            if block == test.exit || mem::replace(&mut seen[block], true) {
                continue;
            }
            let node = &graph.blocks[block];
            match (node.exception_successors.as_slice(), node.exception_predecessors.as_slice()) {
                ([], []) => {}
                ([handler], []) if Some(*handler) == handler_latch => pending.push(*handler),
                ([], _) if Some(block) == handler_latch => {}
                (handlers, entries) if allow_finally
                    && (entries.is_empty() || self.exceptions.counted_loop_finally_entry(block))
                    && handlers.iter().all(|&handler| self.exceptions.counted_loop_finally_dispatch(block, handler)) =>
                {
                    pending.extend_from_slice(handlers);
                }
                _ => return false,
            }
            for index in node.instructions.clone() {
                let op = &instructions[index];
                if self.exceptions.skips_instruction(index) {
                    return false;
                }
                if omitted.contains(&index) {
                    continue;
                }
                if block != header && !matches!(op.opcode, 0 | 0xa7 | 0xc8) {
                    has_body = true;
                }
                if let Some(local) = access(op) {
                    let slot = local.slot();
                    if helpers.contains(&Some(slot))
                        || matches!(local, Access::Store(Kind::Long | Kind::Double, _)
                            if slot.checked_add(1).is_some_and(|high| helpers.contains(&Some(high))))
                    {
                        return false;
                    }
                }
                // A handler-only latch is tied to a proven break edge. The
                // loop emitter checks its merge and requires the false test
                // edge to need no assignment before converting to a `for`.
                if handler_latch.is_none()
                    && let Some(Access::Store(kind, slot)) = access(op)
                {
                    // A different binding at the surviving exit could
                    // require a synthetic assignment on the false test
                    // edge, something a `for` test cannot render.
                    let low = slot.saturating_sub(1);
                    let high =
                        slot.saturating_add(u16::from(matches!(kind, Kind::Long | Kind::Double)));
                    for affected in low..=high {
                        if *live
                            .entry(affected)
                            .or_insert_with(|| self.local_is_live(test.exit, affected))
                        {
                            return false;
                        }
                    }
                }
            }
            pending.extend_from_slice(&node.successors);
        }
        has_body
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Int,
    Long,
    Float,
    Double,
    Ref,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Access {
    Load(Kind, u16),
    Store(Kind, u16),
    Increment(u16),
}

impl Access {
    fn slot(self) -> u16 {
        match self {
            Self::Load(_, slot) | Self::Store(_, slot) | Self::Increment(slot) => slot,
        }
    }
}

pub(super) fn local_slot(op: &Instruction) -> Option<u16> {
    access(op).map(Access::slot)
}

fn access(op: &Instruction) -> Option<Access> {
    const KINDS: [Kind; 5] = [Kind::Int, Kind::Long, Kind::Float, Kind::Double, Kind::Ref];
    let (relative, kind, slot): (u8, fn(Kind, u16) -> Access, u16) = match (op.opcode, &op.operand)
    {
        (op @ 0x15..=0x19, Operand::Local(slot)) => (op - 0x15, Access::Load, *slot),
        (op @ 0x1a..=0x2d, _) => ((op - 0x1a) / 4, Access::Load, u16::from((op - 0x1a) % 4)),
        (op @ 0x36..=0x3a, Operand::Local(slot)) => (op - 0x36, Access::Store, *slot),
        (op @ 0x3b..=0x4e, _) => ((op - 0x3b) / 4, Access::Store, u16::from((op - 0x3b) % 4)),
        (0x84, Operand::Increment { index, .. }) => return Some(Access::Increment(*index)),
        _ => return None,
    };
    Some(kind(KINDS[usize::from(relative)], slot))
}

fn element_kind(ty: &Type) -> Kind {
    element_load(ty).1
}

fn element_load(ty: &Type) -> (u8, Kind) {
    match ty {
        Type::Primitive(Primitive::Int) => (0x2e, Kind::Int),
        Type::Primitive(Primitive::Long) => (0x2f, Kind::Long),
        Type::Primitive(Primitive::Float) => (0x30, Kind::Float),
        Type::Primitive(Primitive::Double) => (0x31, Kind::Double),
        Type::Object(_) | Type::Array(_) => (0x32, Kind::Ref),
        Type::Primitive(Primitive::Boolean | Primitive::Byte) => (0x33, Kind::Int),
        Type::Primitive(Primitive::Char) => (0x34, Kind::Int),
        Type::Primitive(Primitive::Short) => (0x35, Kind::Int),
        Type::Void => unreachable!("void loop element"),
    }
}

fn useful_offsets(instructions: &[Instruction]) -> impl Iterator<Item = u32> + '_ {
    instructions
        .iter()
        .filter(|op| op.opcode != 0)
        .flat_map(|op| op.offset..op.offset + op.len)
}

fn distinct(slots: &[u16]) -> bool {
    slots
        .iter()
        .enumerate()
        .all(|(index, slot)| !slots[..index].contains(slot))
}

fn instance_member<'a>(
    machine: &'a Machine<'_, '_>,
    op: &Instruction,
) -> Option<(&'a str, &'a str, &'a str)> {
    let index = match (op.opcode, &op.operand) {
        (0xb6, Operand::Constant(index)) | (0xb9, Operand::InvokeInterface { index, count: 1 }) => {
            *index
        }
        _ => return None,
    };
    machine.constant_pool().member_ref(index).ok()
}

fn unboxing<'a>(
    entry: &Machine<'_, '_>,
    owner: &str,
    tail: &'a [Instruction],
) -> Option<(Primitive, &'a [Instruction])> {
    let (method, rest) = tail.split_first()?;
    let (declared, method, descriptor) = instance_member(entry, method)?;
    if owner != declared {
        return None;
    }
    let primitive = match (owner, method, descriptor) {
        ("java/lang/Boolean", "booleanValue", "()Z") => Primitive::Boolean,
        ("java/lang/Byte", "byteValue", "()B") => Primitive::Byte,
        ("java/lang/Character", "charValue", "()C") => Primitive::Char,
        ("java/lang/Short", "shortValue", "()S") => Primitive::Short,
        ("java/lang/Integer", "intValue", "()I") => Primitive::Int,
        ("java/lang/Long", "longValue", "()J") => Primitive::Long,
        ("java/lang/Float", "floatValue", "()F") => Primitive::Float,
        ("java/lang/Double", "doubleValue", "()D") => Primitive::Double,
        _ => return None,
    };
    Some((primitive, rest))
}
