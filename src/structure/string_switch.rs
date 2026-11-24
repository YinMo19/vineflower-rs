// Based on Vineflower's SwitchHelper (Apache-2.0).
// Copyright 2000-2020 JetBrains s.r.o.

use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet};
use std::mem;
use std::ops::Range;

use crate::bytecode::{Instruction, Operand};
use crate::cfg::ControlFlowGraph;
use crate::classfile::{Constant, ConstantPool};
use crate::lift::{Effect, Machine, string_literal};
use crate::source_text::Document;

use super::{Emitter, Region, StructureError};

#[cfg(test)]
mod tests;

pub(super) struct Dispatch {
    pub(super) default: u32,
    pub(super) cases: Vec<(i32, u32)>,
    labels: Vec<Label>,
}

struct Label {
    text: String,
    offsets: Range<u32>,
}

impl Dispatch {
    fn new(default: u32, capacity: usize) -> Self {
        Self {
            default,
            cases: Vec::with_capacity(capacity),
            labels: Vec::with_capacity(capacity),
        }
    }

    fn push(&mut self, target: u32, label: Label) {
        // Each label comes from one comparison instruction in this method.
        self.cases.push((self.labels.len() as i32, target));
        self.labels.push(label);
    }

    pub(super) fn label(&self, key: i32) -> (&str, Vec<u32>) {
        let label = &self.labels[key as usize];
        (&label.text, label.offsets.clone().collect())
    }
}

struct Plan {
    prefix_end: usize,
    hash: usize,
    switch: usize,
    dispatch_block: usize,
    helpers: BTreeSet<usize>,
    exits: BTreeSet<usize>,
    alias: u16,
    tag: Option<u16>,
    dispatch: Dispatch,
}

impl Emitter<'_> {
    pub(super) fn try_emit_string_switch<'a, 'c>(
        &mut self,
        block: usize,
        region: Region<'_, 'a, 'c>,
        machine: &mut Machine<'a, 'c>,
        depth: usize,
        pending: &mut Vec<u32>,
    ) -> Result<Option<Option<usize>>, StructureError> {
        if !machine.this_is_initialized() {
            return Ok(None);
        }
        let matcher = Matcher {
            instructions: self.instructions,
            graph: self.graph,
            pool: machine.constant_pool(),
            ascii: machine.ascii_strings(),
        };
        let Some(plan) = matcher.plan(block) else {
            return Ok(None);
        };

        // This is a single-entry region. No other structured transformation may
        // already own or enter one of the blocks the collapse will consume.
        let graph = self.graph;
        let catches = &graph.blocks[block].exception_successors;
        if std::iter::once(block)
            .chain(plan.helpers.iter().copied())
            .any(|helper| {
                let node = &graph.blocks[helper];
                !self.layout.inside(helper, region)
                    || !self.exceptions.contains(region.exception_arm, helper)
                    || self
                        .exceptions
                        .at_start(region.exception_arm, helper)
                        .is_some()
                    || self.exceptions.skips_binding(helper)
                    || self.exceptions.cleanup_prefix(helper) != 0
                    || self
                        .exceptions
                        .finally_range(region.exception_arm, helper)
                        .is_some()
                    || self
                        .exceptions
                        .return_split(region.exception_arm, helper)
                        .is_some()
                    || self.exceptions.monitor_acquisition_end(helper).is_some()
                    || node
                        .instructions
                        .clone()
                        .any(|index| self.exceptions.skips_instruction(index))
                    || self.emitted[helper]
                    || node.exception_successors.as_slice() != catches.as_slice()
                    || !node.exception_predecessors.is_empty()
                    || (helper != block
                        && (self.layout.loops[helper].is_some()
                            || region.loop_transfer(helper).is_some()))
            })
        {
            return Ok(None);
        }
        // All reads of the alias/tag inside the region were matched below. A
        // normal exit or a handler must not observe either removed store.
        for target in plan.exits.iter().chain(catches).copied() {
            if self.local_is_live(target, plan.alias)
                || plan.tag.is_some_and(|tag| self.local_is_live(target, tag))
            {
                return Ok(None);
            }
        }

        let prefix = self.graph.blocks[block].instructions.start..plan.prefix_end;
        let tail = self.lift_range(block, prefix, machine, region, depth, mem::take(pending))?;
        if !matches!(tail.effect, Effect::None) {
            return Err(self.unstructured(block));
        }
        *pending = tail.offsets;

        // The prefix leaves the original receiver on the stack instead of
        // storing/reloading it. Java switch performs the same null check; no
        // non-null path reevaluates the receiver or calls user code in dispatch.
        let dispatch = &self.instructions[plan.switch];
        let control = machine
            .control_order(dispatch)?
            .expect("switch control schedule");
        let selector: Document =
            machine.take_string_switch_selector(&self.instructions[plan.hash])?;
        pending.extend(dispatch.offset..dispatch.offset + dispatch.len);
        self.emitted[block] = true;
        for helper in plan.helpers {
            self.emitted[helper] = true;
        }
        self.emit_switch(
            plan.dispatch_block,
            region,
            machine,
            depth,
            selector,
            pending,
            control,
            Some(&plan.dispatch),
        )
        .map(Some)
    }
}

struct Matcher<'m, 'c> {
    instructions: &'m [Instruction],
    graph: &'m ControlFlowGraph,
    pool: &'m ConstantPool<'c>,
    ascii: bool,
}

struct Bucket {
    hit: usize,
    label: Label,
}

struct Buckets {
    cases: Vec<Bucket>,
    helpers: BTreeSet<usize>,
}

impl Matcher<'_, '_> {
    fn plan(&self, head: usize) -> Option<Plan> {
        let range = &self.graph.blocks[head].instructions;
        let [setup @ .., hash, switch] = &self.instructions[range.clone()] else {
            return None;
        };
        let (default, hashes) = switch_targets(switch)?;
        if hashes.is_empty() || !self.string_call(hash, "hashCode", "()I") {
            return None;
        }
        let hash = range.end - 2;
        let miss = self.graph.block_at(default)?;

        if let [.., alias_store, initial, tag_store, alias_load] = setup
            && let (Some(alias), Some(tag)) = (astore(alias_store), istore(tag_store))
            && alias != tag
            && aload(alias_load) == Some(alias)
            && self.int(initial) == Some(-1)
        {
            return self.split(head, hash - 4, hash, miss, hashes, alias, tag);
        }
        // Eclipse evaluates the selector, duplicates it for its synthetic
        // equality receiver, and dispatches directly to source case bodies.
        let [.., duplicate, alias_store] = setup else {
            return None;
        };
        if duplicate.opcode != 0x59 {
            return None;
        }
        self.direct(head, hash - 2, hash, miss, hashes, astore(alias_store)?)
    }

    fn split(
        &self,
        head: usize,
        prefix_end: usize,
        hash: usize,
        join: usize,
        hashes: &[(i32, u32)],
        alias: u16,
        tag: u16,
    ) -> Option<Plan> {
        let [tag_load, switch] = self.block(join) else {
            return None;
        };
        let (default, tags) = switch_targets(switch)?;
        if iload(tag_load) != Some(tag)
            || tags
                .iter()
                .any(|&(key, target)| key == -1 && target != default)
        {
            return None;
        }
        let Buckets { cases, mut helpers } = self.buckets(join, hashes, alias)?;
        if !helpers.insert(join) {
            return None;
        }
        let mut by_tag = BTreeMap::new();
        for Bucket { hit, label } in cases {
            if !helpers.insert(hit) || self.graph.blocks[hit].successors.as_slice() != [join] {
                return None;
            }
            let (value, store) = match self.block(hit) {
                [value, store] => (value, store),
                [value, store, jump] if is_jump(jump) => (value, store),
                _ => return None,
            };
            let key = self.int(value)?;
            if istore(store) != Some(tag) || key == -1 || by_tag.insert(key, label).is_some() {
                return None;
            }
        }
        let mut dispatch = Dispatch::new(default, by_tag.len());
        for &(key, target) in tags {
            if let Some(label) = by_tag.remove(&key) {
                dispatch.push(target, label);
            } else if target != default {
                return None;
            }
        }
        if !by_tag.is_empty() {
            return None;
        }
        self.finish(
            head,
            Plan {
                prefix_end,
                hash,
                switch: self.graph.blocks[join].instructions.end - 1,
                dispatch_block: join,
                helpers,
                exits: BTreeSet::new(),
                alias,
                tag: Some(tag),
                dispatch,
            },
        )
    }

    fn direct(
        &self,
        head: usize,
        prefix_end: usize,
        hash: usize,
        miss: usize,
        hashes: &[(i32, u32)],
        alias: u16,
    ) -> Option<Plan> {
        let Buckets { cases, helpers } = self.buckets(miss, hashes, alias)?;
        let mut dispatch = Dispatch::new(self.offset(miss), cases.len());
        for Bucket { hit, label } in cases {
            dispatch.push(self.offset(hit), label);
        }
        self.finish(
            head,
            Plan {
                prefix_end,
                hash,
                switch: hash + 1,
                dispatch_block: head,
                helpers,
                exits: BTreeSet::new(),
                alias,
                tag: None,
                dispatch,
            },
        )
    }

    fn finish(&self, head: usize, mut plan: Plan) -> Option<Plan> {
        let dispatch = &plan.dispatch;
        let helpers = &plan.helpers;
        if helpers.contains(&head)
            || helpers.iter().any(|&block| {
                self.graph.blocks[block]
                    .predecessors
                    .iter()
                    .any(|pred| *pred != head && !helpers.contains(pred))
            })
        {
            return None;
        }
        for target in
            std::iter::once(dispatch.default).chain(dispatch.cases.iter().map(|&(_, dest)| dest))
        {
            let block = self.graph.block_at(target)?;
            if block == head || helpers.contains(&block) {
                return None;
            }
            plan.exits.insert(block);
        }
        Some(plan)
    }

    fn buckets(&self, default: usize, hashes: &[(i32, u32)], alias: u16) -> Option<Buckets> {
        let mut helpers = BTreeSet::new();
        let mut seen = BTreeSet::<Cow<'_, [u16]>>::new();
        let mut cases = Vec::new();
        for &(hash, target) in hashes {
            let mut current = self.graph.block_at(target)?;
            while current != default {
                if !helpers.insert(current) {
                    // A bucket may neither reenter another bucket nor loop.
                    return None;
                }
                let ops = self.block(current);
                if let [jump] = ops
                    && is_jump(jump)
                    && self.graph.blocks[current].successors.as_slice() == [default]
                {
                    break;
                }
                let [receiver, literal, equals, branch] = ops else {
                    return None;
                };
                if aload(receiver) != Some(alias)
                    || !self.string_call(equals, "equals", "(Ljava/lang/Object;)Z")
                {
                    return None;
                }
                let units = self.string(literal)?;
                if java_hash(&units) != hash {
                    return None;
                }
                let label = Label {
                    text: string_literal(&units, self.ascii),
                    offsets: literal.offset..literal.offset + literal.len,
                };
                if !seen.insert(units) {
                    return None;
                }
                let &[taken, fallthrough] = self.graph.blocks[current].successors.as_slice() else {
                    return None;
                };
                let (hit, miss) = match branch.opcode {
                    0x99 => (fallthrough, taken),
                    0x9a => (taken, fallthrough),
                    _ => return None,
                };
                cases.push(Bucket { hit, label });
                current = miss;
            }
        }
        (!cases.is_empty()).then_some(Buckets { cases, helpers })
    }

    fn block(&self, block: usize) -> &[Instruction] {
        &self.instructions[self.graph.blocks[block].instructions.clone()]
    }

    fn offset(&self, block: usize) -> u32 {
        self.instructions[self.graph.blocks[block].instructions.start].offset
    }

    fn string_call(&self, op: &Instruction, name: &str, descriptor: &str) -> bool {
        let (0xb6, Operand::Constant(index)) = (op.opcode, &op.operand) else {
            return false;
        };
        matches!(self.pool.get(*index), Ok(Constant::Methodref { .. }))
            && self
                .pool
                .member_ref(*index)
                .is_ok_and(|member| member == ("java/lang/String", name, descriptor))
    }

    fn string(&self, op: &Instruction) -> Option<Cow<'_, [u16]>> {
        let (0x12 | 0x13, Operand::Constant(index)) = (op.opcode, &op.operand) else {
            return None;
        };
        let Constant::String(index) = *self.pool.get(*index).ok()? else {
            return None;
        };
        self.pool.utf16(index).ok()
    }

    fn int(&self, op: &Instruction) -> Option<i32> {
        match (op.opcode, &op.operand) {
            (0x02..=0x08, _) => Some(i32::from(op.opcode) - 3),
            (0x10 | 0x11, Operand::Immediate(value)) => Some(*value),
            (0x12 | 0x13, Operand::Constant(index)) => match self.pool.get(*index).ok()? {
                Constant::Integer(value) => Some(*value),
                _ => None,
            },
            _ => None,
        }
    }
}

fn switch_targets(op: &Instruction) -> Option<(u32, &[(i32, u32)])> {
    let (0xaa | 0xab, Operand::Switch { default, cases }) = (op.opcode, &op.operand) else {
        return None;
    };
    Some((*default, cases))
}

fn local(op: &Instruction, indexed: u8, short: u8) -> Option<u16> {
    if let Operand::Local(slot) = op.operand
        && op.opcode == indexed
    {
        Some(slot)
    } else {
        (short..short + 4)
            .contains(&op.opcode)
            .then(|| u16::from(op.opcode - short))
    }
}

fn aload(op: &Instruction) -> Option<u16> {
    local(op, 0x19, 0x2a)
}
fn astore(op: &Instruction) -> Option<u16> {
    local(op, 0x3a, 0x4b)
}
fn iload(op: &Instruction) -> Option<u16> {
    local(op, 0x15, 0x1a)
}
fn istore(op: &Instruction) -> Option<u16> {
    local(op, 0x36, 0x3b)
}

fn is_jump(op: &Instruction) -> bool {
    matches!(op.opcode, 0xa7 | 0xc8)
}

fn java_hash(units: &[u16]) -> i32 {
    units.iter().fold(0i32, |hash, &unit| {
        hash.wrapping_mul(31).wrapping_add(i32::from(unit))
    })
}
