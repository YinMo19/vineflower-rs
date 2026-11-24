// Based on Vineflower pattern-switch recovery (Apache-2.0).

use std::{collections::{BTreeMap, BTreeSet}, ops::Range};

use crate::{bytecode::{Instruction, Operand}, classfile::{Constant, ConstantPool}, lift::{Effect, Machine}, source_text::Document};

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

    /// A guard owns an acyclic prefix with one successful continuation. Every
    /// failure reaches the retry for this exact bootstrap index; no other
    /// arm, continuation, or exception handler can enter the owned prefix.
    pub(super) fn arm(
        &self, emitter: &Emitter<'_>, entry: usize, first: usize, key: i32, targets: &BTreeSet<usize>,
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
            let (last, prefix) = emitter.instructions.get(start..node.instructions.end)?.split_last()?;
            let bridge = !targets.contains(&block) && node.successors.len() == 1
                && matches!(last.opcode, 0x00 | 0xa7 | 0xc8) && prefix.iter().all(|op| op.opcode == 0);
            if !ancestors.contains(&block) && !bridge {
                if let Some(previous) = success.replace(block) && previous != block {
                    return None;
                }
                continue;
            }
            if !emitter.layout.direct_loop_member(block, self.dispatch)
                || emitter.layout.loops[block].is_some()
                || !matches!(last.opcode, 0x99..=0xa6 | 0xaa..=0xab | 0xc6..=0xc7) && !bridge
                || node.successors.iter().any(|&next| next <= block)
            {
                return None;
            }
            if owned.insert(block) {
                pending.extend_from_slice(&node.successors);
            }
        }
        if reached_retries.is_empty() || owned.iter().chain(&reached_retries).any(|&block| {
            blocks[block].predecessors.iter().any(|pred| {
                !(block == entry && *pred == self.dispatch || owned.contains(pred))
            })
        }) {
            return None;
        }
        Some(Some(Guard::Conditional(ConditionalGuard {
            entry, success: success?, blocks: owned, retries: reached_retries,
        })))
    }

    pub(super) fn owns_all_retries<'g>(&self, guards: impl Iterator<Item = &'g Guard>) -> bool {
        let mut covered = BTreeSet::new();
        guards.flat_map(Guard::retry_blocks).all(|retry| covered.insert(retry))
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

    fn retry_blocks(&self) -> impl Iterator<Item = usize> + '_ {
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

    pub(super) fn document(&self, emitter: &Emitter<'_>, first: usize, machine: &Machine<'_, '_>) -> Option<Document> {
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
    fn document(&self, emitter: &Emitter<'_>, first: usize, machine: &Machine<'_, '_>) -> Option<Document> {
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
        match decision {
            Decision::Expr(doc) => Some(doc),
            Decision::Literal(_) => None,
        }
    }

    fn decision<'a, 'c>(&self, emitter: &Emitter<'_>, mut block: usize, first: usize, machine: &Machine<'a, 'c>, depth: usize) -> Option<Decision> {
        loop {
            if block == self.success { return Some(Decision::Literal(true)); }
            if self.retries.contains(&block) { return Some(Decision::Literal(false)); }
            if !self.blocks.contains(&block) || depth >= 64 { return None; }
            let node = &emitter.graph.blocks[block];
            if block != self.entry && empty_bridge(emitter, block) {
                block = node.successors[0];
                continue;
            }
            let start = if block == self.entry { first } else { node.instructions.start };
            let (terminal, producers) = emitter.instructions[start..node.instructions.end].split_last()?;
            let mut trial = machine.clone();
            for op in producers {
                if !matches!(trial.step(op).ok()?, Effect::None) || !trial.take_prelude().is_empty() {
                    return None;
                }
            }
            let switch_type = trial.pattern_guard_switch_type(terminal);
            let effect = trial.step(terminal).ok()?;
            if !trial.take_prelude().is_empty() || !trial.same_control_stack(machine) || !trial.same_locals(machine) {
                return None;
            }
            let next = |target| self.decision(emitter, target, first, machine, depth + 1);
            let result = match effect {
                Effect::Branch { target, when_true, when_false } => {
                    let (taken, fallthrough) = emitter.branch_targets(block, target).ok()?;
                    Decision::select(when_true, when_false, next(taken)?, next(fallthrough)?)
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
                            Some(Rule {
                                labels, default, statements: Vec::new(), trailing_offsets: Vec::new(),
                                result: RuleResult::Yield(next(emitter.graph.block_at(target)?)?.into_document()),
                            })
                        })
                        .collect::<Option<Vec<_>>>()?;
                    Decision::Expr(SwitchExpression { selector: &selector, rules, depth: 0 }.render())
                }
                _ => return None,
            };
            return Some(result.anchored(emitter.instructions.get(start)?.offset..terminal.offset + terminal.len));
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
    let node = &emitter.graph.blocks[block];
    node.successors.len() == 1 && emitter.instructions[node.instructions.clone()].split_last().is_some_and(|(last, prefix)| {
        matches!(last.opcode, 0x00 | 0xa7 | 0xc8) && prefix.iter().all(|op| op.opcode == 0)
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

enum Decision { Literal(bool), Expr(Document) }

impl Decision {
    fn into_document(self) -> Document {
        match self { Self::Literal(true) => "true".into(), Self::Literal(false) => "false".into(), Self::Expr(doc) => doc }
    }

    fn select(mut condition: Document, inverse: Document, yes: Self, no: Self) -> Self {
        use Decision::Literal;
        Self::Expr(match (yes, no) {
            (Literal(true), Literal(false)) => condition,
            (Literal(false), Literal(true)) => inverse,
            (yes, no) => {
                condition.surround("(", ") ? ");
                condition.append(yes.into_document());
                condition.push_str(" : ");
                condition.append(no.into_document());
                condition
            }
        })
    }

    fn anchored(self, offsets: Range<u32>) -> Self {
        if let Self::Expr(doc) = self {
            let mut result = Document::new();
            result.anchor(offsets);
            result.append(doc);
            Self::Expr(result)
        } else { self }
    }
}
