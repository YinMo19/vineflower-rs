// Based on Vineflower pattern-switch recovery (Apache-2.0).

use std::{collections::{BTreeMap, BTreeSet}, ops::Range};

use crate::{bytecode::{Instruction, Operand}, classfile::{Constant, ConstantPool}, lift::{Effect, IfPatternLocal, Machine, pattern_dispatch::PatternLabel}, source_text::Document};

use super::{Emitter, Head, ends_with_null_check, local, push_zero};
use super::super::switch_expression::{CaseLabel, DefaultLabel, Rule, RuleResult, SwitchExpression};

pub(super) struct RestartLoop {
    pub(super) dispatch: usize,
    retries: BTreeMap<usize, Retry>,
}

struct Retry {
    next_index: i32,
    start: usize,
}

/// The redundant type-test ladder for a comma-separated group of unnamed
/// patterns. Its success continues to user code (possibly a real guard).
pub(super) struct Alternatives {
    pub(super) entry: usize,
    pub(super) tests: Vec<(usize, Option<usize>)>,
    pub(super) retry: usize,
}

impl Alternatives {
    pub(super) fn test_blocks(&self) -> impl Iterator<Item = usize> + '_ {
        self.tests.iter().flat_map(|&(test, bridge)| [Some(test), bridge].into_iter().flatten())
    }

    fn retry_edge(&self, block: usize, pred: usize) -> bool {
        block == self.retry && self.tests.last().is_some_and(|&(test, _)| test == pred)
    }
}

pub(super) enum Guard {
    Never { block: usize, bytes: Range<u32> },
    Conditional(ConditionalGuard),
}

pub(super) struct ConditionalGuard {
    entry: usize,
    success: usize,
    blocks: BTreeSet<usize>,
    retries: BTreeSet<usize>,
}

impl RestartLoop {
    pub(super) fn recognize(emitter: &Emitter<'_>, preheader: usize, pool: &ConstantPool<'_>) -> Option<(Head, Self)> {
        let blocks = &emitter.graph.blocks;
        let pre = &blocks[preheader];
        let &[dispatch] = pre.successors.as_slice() else { return None };
        let header = &blocks[dispatch];
        if dispatch <= preheader || emitter.layout.loops[dispatch].is_none() || !private(emitter, preheader)
            || !private(emitter, dispatch) || header.predecessors.len() < 2
            || !header.predecessors.contains(&preheader)
        {
            return None;
        }
        let [alias_load, restart_load, indy, switch] = &emitter.instructions[header.instructions.clone()] else { return None };
        if indy.opcode != 0xba || !matches!(switch.operand, Operand::Switch { .. }) {
            return None;
        }
        let alias = local(alias_load, false, true)?;
        let restart = local(restart_load, false, false)?;
        if alias == restart { return None; }
        let code = &emitter.instructions[pre.instructions.clone()];
        let keep = if code.last().is_some_and(|op| matches!(op.opcode, 0xa7 | 0xc8)) {
            if code.last()?.operand != Operand::Branch(alias_load.offset) { return None; }
            code.len() - 1
        } else {
            if pre.instructions.end != header.instructions.start { return None; }
            code.len()
        };
        let [prefix @ .., alias_store, zero, store] = &code[..keep] else { return None };
        if local(alias_store, true, true) != Some(alias) || !push_zero(zero) || local(store, true, false) != Some(restart) {
            return None;
        }
        let alias_store = pre.instructions.start + prefix.len();
        let null_check = ends_with_null_check(prefix, pool);
        let setup = alias_store - usize::from(null_check) * 3;
        let mut retries = BTreeMap::new();
        for &retry in header.predecessors.iter().filter(|&&pred| pred != preheader) {
            let node = &blocks[retry];
            let [.., index, store, jump] = &emitter.instructions[node.instructions.clone()] else { return None };
            if !private(emitter, retry) || node.successors.as_slice() != [dispatch]
                || !emitter.layout.direct_loop_member(retry, dispatch)
                || local(store, true, false) != Some(restart) || !matches!(jump.opcode, 0xa7 | 0xc8)
                || jump.operand != Operand::Branch(alias_load.offset)
            {
                return None;
            }
            let next_index = integer(pool, index)?;
            if next_index <= 0 { return None; }
            retries.insert(retry, Retry { next_index, start: node.instructions.end - 3 });
        }
        let head = Head { setup, restart, restart_store: Some(alias_store + 2), alias, alias_store, null_check };
        Some((head, Self { dispatch, retries }))
    }

    pub(super) fn restart_store(&self, index: usize) -> bool {
        self.retries.values().any(|retry| retry.start + 1 == index)
    }

    pub(super) fn alternatives(
        &self,
        emitter: &Emitter<'_>,
        machine: &Machine<'_, '_>,
        target: usize,
        alias: u16,
        keys: &[i32],
        labels: &[PatternLabel],
        targets: &BTreeSet<usize>,
    ) -> Option<Alternatives> {
        let blocks = &emitter.graph.blocks;
        let mut tests = Vec::with_capacity(keys.len());
        let mut entry = None;
        let mut test = target;
        let mut pred = self.dispatch;
        let owned = |block| {
            private(emitter, block) && emitter.layout.direct_loop_member(block, self.dispatch)
                && emitter.layout.loops[block].is_none()
        };
        for &key in keys {
            let PatternLabel::Type(ty) = labels.get(usize::try_from(key).ok()?)? else { return None };
            if test <= pred || !owned(test) || (test != target && targets.contains(&test))
                || blocks[test].predecessors != [pred]
            {
                return None;
            }
            let [load, check, branch] = &emitter.instructions[blocks[test].instructions.clone()] else { return None };
            let Operand::Constant(class) = check.operand else { return None };
            let Operand::Branch(destination) = branch.operand else { return None };
            if check.opcode != 0xc1 || local(load, false, true) != Some(alias)
                || machine.pattern_class(class).ok().as_ref() != Some(ty)
            {
                return None;
            }
            let (taken, fallthrough) = emitter.branch_targets(test, destination).ok()?;
            let (mut matched, failed) = match branch.opcode {
                0x99 => (fallthrough, taken),
                0x9a => (taken, fallthrough),
                _ => return None,
            };
            if matched == failed || matched <= test || failed <= test {
                return None;
            }
            let bridge = (owned(matched) && !targets.contains(&matched)
                && blocks[matched].predecessors == [test] && empty_bridge(emitter, matched))
                .then_some(matched);
            if let Some(bridge) = bridge {
                matched = blocks[bridge].successors[0];
                if matched <= bridge {
                    return None;
                }
            }
            if entry.replace(matched).is_some_and(|previous| previous != matched) {
                return None;
            }
            tests.push((test, bridge));
            pred = test;
            test = failed;
        }
        let retry = self.retries.get(&test)?;
        let entry = entry?;
        let shape = Alternatives { entry, tests, retry: test };
        if retry.start != blocks[test].instructions.start || retry.next_index != keys.last()?.checked_add(1)?
            || targets.contains(&test) || entry == test || targets.contains(&entry)
            || !private(emitter, entry)
            || shape.test_blocks().any(|block| block >= entry)
            || blocks[entry].predecessors.len() != shape.tests.len()
        {
            return None;
        }
        Some(shape)
    }

    /// A guard owns an acyclic prefix with one successful continuation. Every
    /// failure reaches the retry for this exact bootstrap index; no other
    /// arm, continuation, or exception handler can enter the owned prefix.
    pub(super) fn arm(
        &self,
        emitter: &Emitter<'_>,
        entry: usize,
        first: usize,
        key: i32,
        targets: &BTreeSet<usize>,
        alternatives: Option<&Alternatives>,
    ) -> Option<Option<Guard>> {
        let blocks = &emitter.graph.blocks;
        let next_index = key.checked_add(1)?;
        if let Some(retry) = self.retries.get(&entry) {
            // Javac 17's constant-false guard shares a block with an optional
            // verified binding. No instruction between the binding and retry
            // may be skipped, and the dispatch is the only entry.
            return (retry.next_index == next_index
                && retry.start == first
                && blocks[entry].predecessors == [self.dispatch])
                .then(|| Some(Guard::Never {
                    block: entry,
                    bytes: emitter.instructions[first].offset
                        ..emitter.instructions[blocks[entry].instructions.end - 1].offset,
                }));
        }
        let mut ancestors = BTreeSet::new();
        let mut retries = BTreeSet::new();
        let mut pending = Vec::new();
        for (&retry, shape) in &self.retries {
            if shape.next_index == next_index && shape.start == blocks[retry].instructions.start {
                retries.insert(retry);
                pending.extend_from_slice(&blocks[retry].predecessors);
            }
        }
        while let Some(block) = pending.pop() {
            if block < entry || block == self.dispatch || block != entry && targets.contains(&block)
                || !emitter.layout.direct_loop_member(block, self.dispatch) || !ancestors.insert(block)
            {
                continue;
            }
            if block != entry {
                pending.extend_from_slice(&blocks[block].predecessors);
            }
        }
        if !ancestors.contains(&entry) {
            if let Some(shape) = alternatives
                && !blocks[shape.retry].predecessors.iter().all(|&pred| shape.retry_edge(shape.retry, pred))
            {
                return None;
            }
            return Some(None);
        }
        let mut owned = BTreeSet::new();
        let mut reached_retries = BTreeSet::new();
        let mut success = None;
        pending.push(entry);
        while let Some(block) = pending.pop() {
            if retries.contains(&block) {
                reached_retries.insert(block);
                continue;
            }
            if !private(emitter, block) || self.retries.contains_key(&block) {
                return None;
            }
            let node = &blocks[block];
            let start = if block == entry { first } else { node.instructions.start };
            let (last, _) = emitter.instructions.get(start..node.instructions.end)?.split_last()?;
            let bridge = !targets.contains(&block) && empty_transfer(emitter, block, start);
            // The final matching edge may contain just the backing cast,
            // the store, and a transfer. That prologue belongs in the
            // predicate, not in its successful continuation.
            let binding_bridge = !ancestors.contains(&block) && !targets.contains(&block)
                && matches!(node.predecessors.as_slice(), &[pred]
                    if emitter.instanceof_prologue(pred, if pred == entry { first } else { blocks[pred].instructions.start })
                        .is_some_and(|site| site.success == block && empty_transfer(emitter, block, site.body_start())));
            if !ancestors.contains(&block) && !bridge && !binding_bridge {
                if let Some(previous) = success.replace(block) && previous != block {
                    return None;
                }
                continue;
            }
            if !emitter.layout.direct_loop_member(block, self.dispatch)
                || emitter.layout.loops[block].is_some()
                || !matches!(last.opcode, 0x99..=0xa6 | 0xaa..=0xab | 0xc6..=0xc7) && !bridge && !binding_bridge
                || node.successors.iter().any(|&next| next <= block)
            {
                return None;
            }
            if owned.insert(block) {
                pending.extend_from_slice(&node.successors);
            }
        }
        let success = success?;
        if reached_retries.is_empty() || owned.iter().chain(&reached_retries).any(|&block| {
            blocks[block].predecessors.iter().any(|pred| {
                !owned.contains(pred)
                    && !(block == entry && (alternatives.is_some() || *pred == self.dispatch))
                    && !alternatives.is_some_and(|shape| shape.retry_edge(block, *pred))
            })
        }) || alternatives.is_some_and(|shape| {
            targets.contains(&success)
                || blocks[success].predecessors.iter().any(|pred| !owned.contains(pred))
                || !reached_retries.contains(&shape.retry)
                    && blocks[shape.retry].predecessors.iter().any(|&pred| !shape.retry_edge(shape.retry, pred))
        }) {
            return None;
        }
        Some(Some(Guard::Conditional(ConditionalGuard {
            entry, success, blocks: owned, retries: reached_retries,
        })))
    }

    pub(super) fn owns_all_retries(&self, mut retries: impl Iterator<Item = usize>) -> bool {
        let mut covered = BTreeSet::new();
        retries.all(|retry| self.retries.contains_key(&retry) && covered.insert(retry))
            && covered.len() == self.retries.len()
    }
}

impl Guard {
    pub(super) fn success(&self) -> Option<usize> {
        match self {
            Self::Never { .. } => None,
            Self::Conditional(guard) => Some(guard.success),
        }
    }

    pub(super) fn retry_blocks(&self) -> impl Iterator<Item = usize> + '_ {
        let (direct, conditional) = match self {
            Self::Never { block, .. } => (Some(*block), None),
            Self::Conditional(guard) => (None, Some(&guard.retries)),
        };
        direct.into_iter().chain(conditional.into_iter().flatten().copied())
    }

    pub(super) fn blocks(&self) -> impl Iterator<Item = usize> + '_ {
        let decisions = match self {
            Self::Never { .. } => None,
            Self::Conditional(guard) => Some(&guard.blocks),
        };
        decisions.into_iter().flatten().copied().chain(self.retry_blocks())
    }

    pub(super) fn document(&self, emitter: &mut Emitter<'_>, first: usize, machine: &mut Machine<'_, '_>) -> Option<Document> {
        match self {
            Self::Never { bytes, .. } => {
                let mut doc = Document::new();
                doc.anchor(bytes.clone());
                doc.push_str("false");
                Some(doc)
            }
            Self::Conditional(guard) => guard.document(emitter, first, machine),
        }
    }
}

impl ConditionalGuard {
    fn document(&self, emitter: &mut Emitter<'_>, first: usize, machine: &mut Machine<'_, '_>) -> Option<Document> {
        let mut counts = BTreeMap::<usize, usize>::new();
        for &block in &self.blocks {
            for &next in &emitter.graph.blocks[block].successors {
                if self.blocks.contains(&next) { *counts.entry(next).or_default() += 1; }
            }
        }
        // A shared executable subgraph cannot be copied into both sides of a
        // source conditional. Empty goto chains may be bypassed instead.
        if counts.into_iter().any(|(block, count)| count > 1 && !empty_bridge(emitter, block)) {
            return None;
        }
        let decision = self.decision(emitter, self.entry, first, machine, 0)?;
        let Decision::Expr { text, bindings } = decision else { return None };
        if !bindings.is_empty() && (emitter.graph.blocks[self.success].predecessors.iter().any(|pred| !self.blocks.contains(pred))
            || bindings.iter().any(|local| self.retries.iter().any(|&retry| emitter.local_is_live(retry, local.slot()))))
        {
            return None;
        }
        for local in bindings.into_iter().rev() {
            machine.install_if_pattern_local(&local);
        }
        Some(text)
    }

    fn decision(&self, emitter: &mut Emitter<'_>, mut block: usize, mut first: usize, machine: &Machine<'_, '_>, depth: usize) -> Option<Decision> {
        loop {
            if block == self.success { return Some(Decision::Literal(true)); }
            if self.retries.contains(&block) { return Some(Decision::Literal(false)); }
            if !self.blocks.contains(&block) || depth >= 64 { return None; }
            let node = &emitter.graph.blocks[block];
            if empty_transfer(emitter, block, first) {
                block = node.successors[0];
                first = emitter.graph.blocks[block].instructions.start;
                continue;
            }
            let end = node.instructions.end;
            let mut trial = machine.clone();
            let prologue = emitter.instanceof_prologue(block, first).filter(|site| self.blocks.contains(&site.success));
            let binding = if let Some(site) = &prologue {
                Some(emitter.lift_guard_instanceof(block, first, site, &mut trial)?)
            } else {
                for op in &emitter.instructions[first..end - 1] {
                    if !matches!(trial.step(op).ok()?, Effect::None) || !trial.take_prelude().is_empty() {
                        return None;
                    }
                }
                None
            };
            let terminal = &emitter.instructions[end - 1];
            let switch_type = trial.pattern_guard_switch_type(terminal);
            let effect = trial.step(terminal).ok()?;
            if !trial.take_prelude().is_empty() || !trial.same_control_stack(machine) || !trial.same_locals(machine) {
                return None;
            }
            let bytes = emitter.instructions.get(first)?.offset..terminal.offset + terminal.len;
            let next = |emitter: &mut Emitter<'_>, target: usize, state: &Machine<'_, '_>| {
                self.decision(emitter, target, emitter.graph.blocks[target].instructions.start, state, depth + 1)
            };
            let result = match effect {
                Effect::Branch { target, when_true, when_false } => {
                    let (taken, fallthrough) = emitter.branch_targets(block, target).ok()?;
                    if let (Some(site), Some(binding)) = (prologue, binding) {
                        let (matched, unmatched, condition) = if taken == site.success {
                            (taken, fallthrough, when_true)
                        } else {
                            (fallthrough, taken, when_false)
                        };
                        // Only a conjunction exports a successful binding
                        // to both the rest of the predicate and the case body.
                        if !matches!(next(emitter, unmatched, machine)?, Decision::Literal(false)) {
                            return None;
                        }
                        let start = site.body_start();
                        let range = site.instructions();
                        let end = if empty_transfer(emitter, matched, start) {
                            emitter.graph.blocks[matched].instructions.end
                        } else {
                            range.end
                        };
                        let terminal = &emitter.instructions[end - 1];
                        let prologue_bytes = emitter.instructions[range.start].offset..terminal.offset + terminal.len;
                        trial.install_if_pattern_local(&binding);
                        let rest = self.decision(emitter, matched, start, &trial, depth + 1)?;
                        let (mut text, mut bindings) = Decision::and(condition, rest)?;
                        text = Decision::anchor(text, prologue_bytes);
                        bindings.push(binding);
                        Decision::Expr { text, bindings }
                    } else {
                        Decision::select(when_true, when_false, next(emitter, taken, machine)?, next(emitter, fallthrough, machine)?)?
                    }
                }
                Effect::Switch { selector } => {
                    let Operand::Switch { default, cases } = &terminal.operand else { return None };
                    let ty = switch_type.as_ref()?;
                    let mut groups = BTreeMap::<u32, Vec<CaseLabel>>::new();
                    for &(key, target) in cases {
                        if target != *default {
                            groups.entry(target).or_default().push(CaseLabel {
                                text: machine.pattern_guard_case(key, ty)?.into(), offsets: Vec::new(),
                            });
                        }
                    }
                    let rules = groups.iter().map(|(&target, labels)| (target, labels.as_slice(), DefaultLabel::Absent))
                        .chain([(*default, &[] as &[CaseLabel], DefaultLabel::Default)])
                        .map(|(target, labels, default)| {
                            let text = next(emitter, emitter.graph.block_at(target)?, machine)?.into_document()?;
                            Some(Rule {
                                labels, default, statements: Vec::new(), trailing_offsets: Vec::new(),
                                result: RuleResult::Yield(text),
                            })
                        })
                        .collect::<Option<Vec<_>>>()?;
                    Decision::expr(SwitchExpression { selector: &selector, rules, depth: 0 }.render())
                }
                _ => return None,
            };
            return Some(result.anchored(bytes));
        }
    }
}

fn private(emitter: &Emitter<'_>, block: usize) -> bool {
    let node = &emitter.graph.blocks[block];
    !emitter.emitted[block] && node.exception_successors.is_empty() && node.exception_predecessors.is_empty()
        && !emitter.assertion_starts(block)
        && node.instructions.clone().all(|index| !emitter.exceptions.skips_instruction(index))
}

fn empty_bridge(emitter: &Emitter<'_>, block: usize) -> bool {
    empty_transfer(emitter, block, emitter.graph.blocks[block].instructions.start)
}

fn empty_transfer(emitter: &Emitter<'_>, block: usize, first: usize) -> bool {
    let node = &emitter.graph.blocks[block];
    let code = &emitter.instructions[first..node.instructions.end];
    node.successors.len() == 1 && (code.is_empty() || code.split_last().is_some_and(|(last, prefix)| {
        matches!(last.opcode, 0x00 | 0xa7 | 0xc8) && prefix.iter().all(|op| op.opcode == 0)
    }))
}

fn integer(pool: &ConstantPool<'_>, op: &Instruction) -> Option<i32> {
    match (op.opcode, &op.operand) {
        (0x02..=0x08, _) => Some(i32::from(op.opcode) - 3),
        (0x10 | 0x11, Operand::Immediate(value)) => Some(*value),
        (0x12 | 0x13, Operand::Constant(index)) => match pool.get(*index).ok()? { Constant::Integer(value) => Some(*value), _ => None },
        _ => None,
    }
}

enum Decision {
    Literal(bool),
    // Reverse evaluation order, so a dominating binding can append itself.
    Expr { text: Document, bindings: Vec<IfPatternLocal> },
}

impl Decision {
    fn expr(text: Document) -> Self {
        Self::Expr { text, bindings: Vec::new() }
    }

    fn into_document(self) -> Option<Document> {
        match self {
            Self::Literal(true) => Some("true".into()),
            Self::Literal(false) => Some("false".into()),
            Self::Expr { text, bindings } => bindings.is_empty().then_some(text),
        }
    }

    fn has_bindings(&self) -> bool {
        matches!(self, Self::Expr { bindings, .. } if !bindings.is_empty())
    }

    fn and(mut condition: Document, rest: Self) -> Option<(Document, Vec<IfPatternLocal>)> {
        match rest {
            Self::Literal(true) => Some((condition, Vec::new())),
            Self::Literal(false) => None,
            Self::Expr { text, bindings } => {
                condition.surround("(", ") && (");
                condition.append(text);
                condition.push(')');
                Some((condition, bindings))
            }
        }
    }

    fn select(mut condition: Document, inverse: Document, yes: Self, no: Self) -> Option<Self> {
        use Decision::Literal;
        Some(match (yes, no) {
            (Literal(true), Literal(false)) => Self::expr(condition),
            (Literal(false), Literal(true)) => Self::expr(inverse),
            (yes, Literal(false)) if yes.has_bindings() => {
                let (text, bindings) = Self::and(condition, yes)?;
                Self::Expr { text, bindings }
            }
            (Literal(false), no) if no.has_bindings() => {
                let (text, bindings) = Self::and(inverse, no)?;
                Self::Expr { text, bindings }
            }
            (yes, no) => {
                condition.surround("(", ") ? ");
                condition.append(yes.into_document()?);
                condition.push_str(" : ");
                condition.append(no.into_document()?);
                Self::expr(condition)
            }
        })
    }

    fn anchor(text: Document, offsets: Range<u32>) -> Document {
        let mut result = Document::new();
        result.anchor(offsets);
        result.append(text);
        result
    }

    fn anchored(self, offsets: Range<u32>) -> Self {
        match self {
            Self::Expr { text, bindings } => Self::Expr { text: Self::anchor(text, offsets), bindings },
            literal => literal,
        }
    }
}
