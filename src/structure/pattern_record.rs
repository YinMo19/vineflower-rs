// Based on Vineflower's SwitchPatternMatchProcessor (Apache-2.0).

use std::{cell::RefCell, collections::{BTreeMap, BTreeSet}};

use crate::{
    bytecode::{Instruction, Operand},
    cfg::ControlFlowGraph,
    classfile::{Constant, ConstantPool, ExceptionHandler},
    descriptor::{Primitive, Type},
    lift::{LiftError, Machine, pattern_dispatch::PatternLabel},
    source_text::Document,
};
use super::pattern_switch::{Head, local, push_zero};

#[cfg(test)]
#[path = "pattern_record_tests.rs"]
mod tests;

pub(super) struct Plans {
    arms: BTreeMap<(u32, u32), RecordArm>,
    claimed: RefCell<BTreeSet<(u32, u32)>>,
}

pub(super) struct RecordArm {
    label: Pattern,
    pub(super) offsets: Vec<u32>,
    pub(super) may_fail: bool,
}

enum Pattern {
    Record(Type, Vec<Pattern>),
    Binding { ty: Type, store: Instruction, cast: Option<Instruction>, slot: u16 },
}

impl Pattern {
    fn render(&self, machine: &mut Machine<'_, '_>) -> Result<Document, LiftError> {
        match self {
            Self::Binding { ty, store, cast, slot } => machine.pattern_binding(ty, Some((store, cast.as_ref(), *slot)), store.offset),
            Self::Record(ty, children) => {
                let mut text = Document::from(machine.pattern_record_type(ty));
                let children = children.iter().map(|child| child.render(machine)).collect::<Result<Vec<_>, _>>()?;
                text.append(Document::relative_delimited(children));
                Ok(text)
            }
        }
    }
}

impl RecordArm {
    pub(super) fn render(&self, entry: &mut Machine<'_, '_>) -> Result<Document, LiftError> {
        self.label.render(entry)
    }
}

impl Plans {
    pub(super) fn get(&self, dispatch: u32, block: u32) -> Option<&RecordArm> {
        self.arms.get(&(dispatch, block))
    }

    pub(super) fn claim(&self, dispatch: u32, block: u32) {
        if self.get(dispatch, block).is_some() {
            self.claimed.borrow_mut().insert((dispatch, block));
        }
    }

    pub(super) fn all_claimed(&self) -> bool {
        self.claimed.borrow().len() == self.arms.len()
    }

    /// Collapse exactly the verified deconstruction prefixes. Offsets of the
    /// remaining instructions are unchanged. No ordinary exception handler is
    /// discarded: every row must protect one accepted record accessor only.
    pub(super) fn prove(
        instructions: &[Instruction], graph: &ControlFlowGraph, handlers: &[ExceptionHandler], machine: &mut Machine<'_, '_>,
    ) -> Option<(Vec<Instruction>, ControlFlowGraph, Self)> {
        if handlers.is_empty() || !machine.can_project_record_patterns() {
            return None;
        }
        let at = |offset| instructions.binary_search_by_key(&offset, |op| op.offset).ok();
        let pool = machine.constant_pool();
        let first_temporary = machine.pattern_raw_parameter_slots();
        let mut accesses = BTreeSet::new();
        let mut wrappers = BTreeMap::new();
        for handler in handlers {
            let start = at(u32::from(handler.start_pc))?;
            let op = &instructions[start];
            let target = graph.block_at(u32::from(handler.handler_pc))?;
            if op.opcode != 0xb6 || op.offset + op.len != u32::from(handler.end_pc)
                || pool.class_name(handler.catch_type).ok()? != "java/lang/Throwable"
                || !accesses.insert(start)
            {
                return None;
            }
            if let std::collections::btree_map::Entry::Vacant(entry) = wrappers.entry(target) {
                let wrapper = &graph.blocks[target];
                if !wrapper.predecessors.is_empty() || !wrapper.successors.is_empty() || !wrapper.exception_successors.is_empty()
                    || !match_wrapper(pool, &instructions[wrapper.instructions.clone()])
                {
                    return None;
                }
                entry.insert(wrapper.instructions.clone());
            }
        }
        let mut removed = vec![false; instructions.len()];
        for range in wrappers.values() {
            removed[range.clone()].fill(true);
        }
        let mut plans = Self { arms: BTreeMap::new(), claimed: RefCell::new(BTreeSet::new()) };
        let mut replacements = BTreeMap::new();
        let mut consumed_accesses = BTreeSet::new();
        let mut dead = Vec::new();
        let mut retry_owners = BTreeMap::new();
        let mut dispatch_headers = BTreeMap::new();
        for (dispatch_block, block) in graph.blocks.iter().enumerate() {
            let range = block.instructions.clone();
            let Some(indy) = range.end.checked_sub(2).filter(|index| *index >= range.start) else { continue };
            let [invoke, switch] = &instructions[indy..range.end] else { continue };
            let Operand::Switch { default, cases } = &switch.operand else { continue };
            if invoke.opcode != 0xba { continue; }
            let Some(dispatch) = machine.read_pattern_dispatch(invoke).ok()? else { continue; };
            let (alias, restart, preheader) = if let Some(head) = Head::recognize(instructions, range.clone(), pool) {
                (head.alias(), None, None)
            } else {
                let Some((alias, restart, preheader)) = restart_head(instructions, graph, dispatch_block) else { continue; };
                (alias, Some(restart), Some(preheader))
            };
            for &(key, target) in cases {
                let Ok(index) = usize::try_from(key) else { continue; };
                if target == *default { continue; }
                let Some(PatternLabel::Type(ty)) = dispatch.labels.get(index) else { continue; };
                let start = at(target)?;
                let start_block = graph.block_at(target)?;
                if graph.blocks[start_block].predecessors != [dispatch_block]
                    || !graph.blocks[start_block].exception_predecessors.is_empty()
                    || removed[start]
                {
                    continue;
                }
                let mut parser = Prefix {
                    instructions, graph, pool, accesses: &accesses, machine,
                    pos: start, alias, restart, dispatch: dispatch_block, key,
                    first_temporary,
                    temporaries: BTreeSet::new(), receivers: BTreeSet::new(), leaves: BTreeSet::new(),
                    used_accesses: BTreeSet::new(), retries: BTreeSet::new(), may_fail: false,
                };
                let Some((label, resume)) = parser.root(ty) else { continue };
                if parser.used_accesses.is_empty() { continue; }
                let layout = parser.pos;
                let owned: BTreeSet<_> = (start..layout).chain(parser.retries.iter().flat_map(|&block| graph.blocks[block].instructions.clone())).collect();
                if !owns_prefix(instructions, graph, dispatch_block, start, resume, &owned, &parser.retries)
                    || owned.iter().any(|&index| removed[index])
                {
                    return None;
                }
                for &retry in &parser.retries {
                    if retry_owners.insert(retry, dispatch_block).is_some() { return None; }
                }
                if let Some(preheader) = preheader { dispatch_headers.insert(dispatch_block, preheader); }
                consumed_accesses.append(&mut parser.used_accesses);
                dead.push(SlotProof {
                    resume, dispatch: dispatch_block, key,
                    hidden: std::mem::take(&mut parser.temporaries),
                    partial_bindings: parser.may_fail.then(|| std::mem::take(&mut parser.leaves)),
                });
                for &index in &owned { removed[index] = true; }
                let mut offsets = Vec::new();
                for index in owned {
                    let op = &instructions[index];
                    offsets.extend(op.offset..op.offset + op.len);
                }
                if replacements.insert(start, instructions[resume].offset).is_some()
                    || plans.arms.insert((switch.offset, target), RecordArm { label, offsets, may_fail: parser.may_fail }).is_some()
                {
                    return None;
                }
            }
        }
        if plans.arms.is_empty() || accesses != consumed_accesses {
            return None;
        }
        for (header, preheader) in dispatch_headers {
            if graph.blocks[header].predecessors.iter().any(|pred| *pred != preheader && retry_owners.get(pred) != Some(&header)) {
                return None;
            }
        }
        let mut projected = Vec::with_capacity(instructions.len());
        for (index, op) in instructions.iter().enumerate() {
            if let Some(&destination) = replacements.get(&index) {
                // This is CFG-only; keep the old start offset and source byte
                // width so lifted code and debug output remain in the old space.
                projected.push(Instruction { opcode: 0xa7, operand: Operand::Branch(destination), ..op.clone() });
            } else if !removed[index] {
                projected.push(op.clone());
            }
        }
        let new_graph = ControlFlowGraph::build(&projected, &[]).ok()?;
        let by_start: BTreeMap<_, _> = plans.arms.iter().map(|(&(_, start), arm)| (start, &arm.label)).collect();
        for SlotProof { resume, dispatch, key, hidden, partial_bindings } in dead {
            let success = new_graph.block_at(instructions[resume].offset)?;
            if !temps_are_dead(&projected, &new_graph, &by_start, &[success], &hidden) {
                return None;
            }
            if let Some(mut partial) = partial_bindings {
                partial.extend(hidden);
                let switch = graph.blocks[dispatch].instructions.end.checked_sub(1)?;
                let Operand::Switch { default, cases } = &instructions[switch].operand else { return None };
                // A failed component can expose neither a scratch store nor
                // a successful binding of an earlier component to later arms.
                let starts = std::iter::once(*default)
                    .chain(cases.iter().filter_map(|&(later, target)| (later > key).then_some(target)))
                    .map(|target| new_graph.block_at(target))
                    .collect::<Option<Vec<_>>>()?;
                if !temps_are_dead(&projected, &new_graph, &by_start, &starts, &partial) {
                    return None;
                }
            }
        }
        Some((projected, new_graph, plans))
    }
}

struct SlotProof {
    resume: usize,
    dispatch: usize,
    key: i32,
    hidden: BTreeSet<u16>,
    partial_bindings: Option<BTreeSet<u16>>,
}

fn restart_head(
    instructions: &[Instruction], graph: &ControlFlowGraph, block: usize,
) -> Option<(u16, u16, usize)> {
    let node = &graph.blocks[block];
    let [selector, restart, _, _] = &instructions[node.instructions.clone()] else { return None };
    let alias = local(selector, false, true)?;
    let restart = local(restart, false, false)?;
    let preheader = block.checked_sub(1)?;
    if alias == restart || !node.predecessors.contains(&preheader) || graph.blocks[preheader].successors != [block] {
        return None;
    }
    let before = &instructions[graph.blocks[preheader].instructions.clone()];
    if before.last().is_some_and(|op| matches!(op.opcode, 0xa7 | 0xc8)) {
        return None;
    }
    let [.., store_alias, zero, store_restart] = before else { return None };
    (local(store_alias, true, true) == Some(alias) && push_zero(zero) && local(store_restart, true, false) == Some(restart))
        .then_some((alias, restart, preheader))
}

struct Prefix<'s, 'm, 'a, 'c> {
    instructions: &'s [Instruction], graph: &'s ControlFlowGraph, pool: &'s ConstantPool<'a>,
    accesses: &'s BTreeSet<usize>, machine: &'m Machine<'a, 'c>,
    pos: usize, alias: u16, restart: Option<u16>, dispatch: usize, key: i32,
    first_temporary: u16,
    temporaries: BTreeSet<u16>, receivers: BTreeSet<u16>, leaves: BTreeSet<u16>,
    used_accesses: BTreeSet<usize>, retries: BTreeSet<usize>, may_fail: bool,
}

impl Prefix<'_, '_, '_, '_> {
    fn take(&mut self) -> Option<&Instruction> {
        let op = self.instructions.get(self.pos)?;
        self.pos += 1;
        Some(op)
    }

    fn root(&mut self, ty: &Type) -> Option<(Pattern, usize)> {
        let alias = self.alias;
        if local(self.take()?, false, true)? != alias { return None; }
        let cast = self.take()?.clone();
        if cast_type(self.machine, &cast, 0xc0)? != *ty { return None; }
        let slot = local(self.take()?, true, true)?;
        let label = self.record(ty, slot, 0)?;
        let mut resume = self.pos;
        if let Some(Instruction { opcode: 0xa7 | 0xc8, operand: Operand::Branch(target), .. }) = self.instructions.get(self.pos) {
            let destination = self.instructions.binary_search_by_key(target, |op| op.offset).ok()?;
            if destination > self.pos && (self.pos + 1..destination).all(|index| {
                self.retries.iter().any(|&retry| self.graph.blocks[retry].instructions.contains(&index))
            }) {
                self.pos += 1;
                resume = destination;
            }
        }
        self.instructions.get(resume)?;
        Some((label, resume))
    }

    fn record(&mut self, ty: &Type, slot: u16, depth: usize) -> Option<Pattern> {
        if depth == 32 || !self.temporary(slot, 1) || !self.receivers.insert(slot) { return None; }
        let Type::Object(owner) = ty else { return None };
        let machine = self.machine;
        let components = machine.pattern_record_components(ty)?;
        let mut labels = Vec::with_capacity(components.len());
        for (name, expected) in components {
            if local(self.take()?, false, true)? != slot { return None; }
            let accessor_index = self.pos;
            let op = self.take()?.clone();
            let (called, method, desc) = method_ref(self.pool, &op, 0xb6)?;
            if called != owner || method != name || Type::parse(desc.strip_prefix("()")?).ok()? != expected
                || !self.accesses.contains(&accessor_index)
                || !self.used_accesses.insert(accessor_index)
            {
                return None;
            }
            labels.push(self.component(expected, depth)?);
        }
        self.receivers.remove(&slot);
        Some(Pattern::Record(ty.clone(), labels))
    }

    fn component(&mut self, expected: Type, depth: usize) -> Option<Pattern> {
        let (kind, width) = kind(&expected)?;
        let stored = self.take()?.clone();
        let scratch = typed_local(&stored, true, kind)?;
        if !self.temporary(scratch, width) { return None; }
        if typed_local(self.take()?, false, kind)? != scratch { return None; }
        if kind == 4 && self.instructions.get(self.pos)?.opcode == 0xc1 {
            let test = self.take()?.clone();
            let narrowed = cast_type(self.machine, &test, 0xc1)?;
            if !self.machine.pattern_covers(&expected, &narrowed) { return None; }
            let retry = self.take()?.clone();
            self.retry(&retry, true)?;
            if typed_local(self.take()?, false, kind)? != scratch { return None; }
            let cast = if self.instructions.get(self.pos)?.opcode == 0xc0 {
                let cast = self.take()?.clone();
                if cast_type(self.machine, &cast, 0xc0)? != narrowed { return None; }
                Some(cast)
            } else if expected == narrowed {
                None
            } else { return None; };
            let binding = self.take()?.clone();
            let binding_slot = typed_local(&binding, true, kind)?;
            if self.looks_like_record_component(binding_slot) {
                return self.record(&narrowed, binding_slot, depth + 1);
            }
            if expected == narrowed || !self.leaf(binding_slot, width) { return None; }
            return Some(Pattern::Binding { ty: narrowed, store: binding, cast, slot: binding_slot });
        }
        let mut binding = self.take()?.clone();
        let mut slot = typed_local(&binding, true, kind)?;
        // javac 25 may copy a component through a throwaway carrier before
        // its constant-true match-test for a total component pattern.
        if self.instructions.get(self.pos)?.opcode == 0x04
            && self.instructions.get(self.pos + 1)?.opcode == 0x99
        {
            if self.instructions.get(self.pos + 2).and_then(|op| typed_local(op, false, kind)) != Some(scratch)
                || !self.temporary(slot, width)
            {
                return None;
            }
            self.pos += 1;
            let retry = self.take()?.clone();
            self.retry(&retry, false)?;
            self.pos += 1;
            binding = self.take()?.clone();
            slot = typed_local(&binding, true, kind)?;
        }
        if !self.leaf(slot, width) { return None; }
        Some(Pattern::Binding { ty: expected, store: binding, cast: None, slot })
    }

    fn looks_like_record_component(&self, receiver: u16) -> bool {
        self.instructions.get(self.pos).is_some_and(|op| local(op, false, true) == Some(receiver))
            && self.accesses.contains(&(self.pos + 1))
    }

    fn retry(&mut self, op: &Instruction, real: bool) -> Option<()> {
        if op.opcode != 0x99 { return None; }
        let Operand::Branch(target) = op.operand else { return None };
        let block = self.graph.block_at(target)?;
        let node = &self.graph.blocks[block];
        let [index, store, jump] = &self.instructions[node.instructions.clone()] else { return None };
        if integer(self.pool, index)? != self.key.checked_add(1)?
            || local(store, true, false)? != self.restart?
            || !matches!(jump.opcode, 0xa7 | 0xc8) || node.successors != [self.dispatch]
            || !node.exception_predecessors.is_empty() || !node.exception_successors.is_empty()
        { return None; }
        self.retries.insert(block);
        self.may_fail |= real;
        Some(())
    }

    fn temporary(&mut self, slot: u16, width: u16) -> bool {
        let Some(end) = slot.checked_add(width) else { return false; };
        let slots = slot..end;
        if slots.clone().any(|slot| self.reserved(slot) || self.receivers.contains(&slot) || self.leaves.contains(&slot)) {
            return false;
        }
        self.temporaries.extend(slots);
        true
    }

    fn leaf(&mut self, slot: u16, width: u16) -> bool {
        let Some(end) = slot.checked_add(width) else { return false };
        let slots = slot..end;
        if slots.clone().any(|slot| self.reserved(slot) || self.temporaries.contains(&slot) || self.leaves.contains(&slot)) {
            return false;
        }
        self.leaves.extend(slots);
        true
    }

    fn reserved(&self, slot: u16) -> bool {
        slot < self.first_temporary || slot == self.alias || Some(slot) == self.restart
    }
}

fn owns_prefix(
    instructions: &[Instruction], graph: &ControlFlowGraph, dispatch: usize, start: usize, resume: usize,
    owned: &BTreeSet<usize>, retries: &BTreeSet<usize>,
) -> bool {
    let first = instructions[start].offset;
    let continuation = instructions[resume].offset;
    let continuation_block = graph.block_at(continuation);
    for (block, node) in graph.blocks.iter().enumerate() {
        if Some(block) == continuation_block || node.instructions.clone().any(|index| owned.contains(&index)) {
            if !node.exception_predecessors.is_empty() || node.predecessors.iter().any(|&pred| {
                let edge = graph.blocks[pred].instructions.end - 1;
                !owned.contains(&edge) && !(pred == dispatch && node.instructions.start == start)
            }) { return false; }
            if retries.contains(&block) && node.predecessors.is_empty() { return false; }
        }
    }
    for (index, op) in instructions.iter().enumerate() {
        let targets: &[u32] = match &op.operand { Operand::Branch(target) => std::slice::from_ref(target), _ => &[] };
        let check = |target| {
            let Ok(destination) = instructions.binary_search_by_key(&target, |op| op.offset) else { return false; };
            if owned.contains(&index) {
                owned.contains(&destination) || target == continuation
                    || matches!(op.opcode, 0xa7 | 0xc8) && graph.block_at(target) == Some(dispatch)
                    && retries.iter().any(|&block| graph.blocks[block].instructions.contains(&index))
            } else {
                !owned.contains(&destination) || target == first && graph.blocks[dispatch].instructions.contains(&index)
            }
        };
        if !targets.iter().all(|&target| check(target)) { return false; }
        if let Operand::Switch { default, cases } = &op.operand
            && (!check(*default) || !cases.iter().all(|&(_, target)| check(target)))
        { return false; }
    }
    true
}

fn temps_are_dead(
    instructions: &[Instruction], graph: &ControlFlowGraph, by_start: &BTreeMap<u32, &Pattern>,
    pending: &[usize], slots: &BTreeSet<u16>,
) -> bool {
    for &slot in slots {
        let mut work = pending.to_vec();
        let mut seen = BTreeSet::new();
        while let Some(block) = work.pop() {
            if !seen.insert(block) { continue; }
            let node = &graph.blocks[block];
            let code = &instructions[node.instructions.clone()];
            if by_start.get(&code[0].offset).is_some_and(|pattern| pattern.defines(slot)) {
                continue;
            }
            let mut killed = false;
            for op in code {
                if let Some((index, width, write, reads)) = local_use(op)
                    && slot >= index && slot - index < width
                {
                    if reads { return false; }
                    if write { killed = true; break; }
                }
            }
            if !killed { work.extend_from_slice(&node.successors); }
        }
    }
    true
}

impl Pattern {
    fn defines(&self, slot: u16) -> bool {
        match self {
            Self::Binding { ty, slot: start, .. } => (*start..*start + ty.slots()).contains(&slot),
            Self::Record(_, children) => children.iter().any(|child| child.defines(slot)),
        }
    }
}

fn local_use(op: &Instruction) -> Option<(u16, u16, bool, bool)> {
    if let Operand::Increment { index, .. } = op.operand { return Some((index, 1, true, true)); }
    for kind in 0..5 {
        for write in [false, true] {
            if let Some(slot) = typed_local(op, write, kind) {
                return Some((slot, if matches!(kind, 1 | 3) { 2 } else { 1 }, write, !write));
            }
        }
    }
    None
}

fn typed_local(op: &Instruction, write: bool, kind: u8) -> Option<u16> {
    let (wide, compact) = if write { (0x36, 0x3b) } else { (0x15, 0x1a) };
    if op.opcode == wide + kind {
        let Operand::Local(slot) = op.operand else { return None };
        return Some(slot);
    }
    let first = compact + kind * 4;
    (first..first + 4).contains(&op.opcode).then(|| u16::from(op.opcode - first))
}

fn kind(ty: &Type) -> Option<(u8, u16)> {
    Some(match ty {
        Type::Primitive(Primitive::Long) => (1, 2),
        Type::Primitive(Primitive::Float) => (2, 1),
        Type::Primitive(Primitive::Double) => (3, 2),
        Type::Primitive(_) => (0, 1),
        Type::Object(_) | Type::Array(_) => (4, 1),
        Type::Void => return None,
    })
}

fn integer(pool: &ConstantPool<'_>, op: &Instruction) -> Option<i32> {
    match (op.opcode, &op.operand) {
        (0x02..=0x08, _) => Some(i32::from(op.opcode) - 3),
        (0x10 | 0x11, Operand::Immediate(value)) => Some(*value),
        (0x12 | 0x13, Operand::Constant(index)) => match pool.get(*index).ok()? { Constant::Integer(value) => Some(*value), _ => None },
        _ => None,
    }
}

fn cast_type(machine: &Machine<'_, '_>, op: &Instruction, opcode: u8) -> Option<Type> {
    let Operand::Constant(index) = op.operand else { return None; };
    (op.opcode == opcode).then(|| machine.pattern_class(index).ok()).flatten()
}

fn match_wrapper(pool: &ConstantPool<'_>, code: &[Instruction]) -> bool {
    let [store, new, dup, load, stringify, cause, construct, throw] = code else { return false; };
    let Operand::Constant(index) = new.operand else { return false; };
    let Some(slot) = local(store, true, true) else { return false; };
    new.opcode == 0xbb && pool.class_name(index).ok() == Some("java/lang/MatchException") && dup.opcode == 0x59
        && local(load, false, true) == Some(slot) && local(cause, false, true) == Some(slot)
        && method_ref(pool, stringify, 0xb6) == Some(("java/lang/Throwable", "toString", "()Ljava/lang/String;"))
        && method_ref(pool, construct, 0xb7) == Some(("java/lang/MatchException", "<init>", "(Ljava/lang/String;Ljava/lang/Throwable;)V"))
        && throw.opcode == 0xbf
}

fn method_ref<'s>(pool: &'s ConstantPool<'_>, op: &Instruction, opcode: u8) -> Option<(&'s str, &'s str, &'s str)> {
    let Operand::Constant(index) = op.operand else { return None; };
    if op.opcode != opcode || !matches!(pool.get(index).ok()?, Constant::Methodref { .. }) { return None; }
    pool.member_ref(index).ok()
}
