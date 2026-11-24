//! Fold closed JVM decision graphs into Java short-circuit conditions.

use std::collections::{BTreeMap, BTreeSet};
use std::ops::RangeInclusive;

use crate::bytecode::{Instruction, Operand};
use crate::lift::{Effect, Machine};
use crate::source_text::{Document, Infix};

use super::{Condition, Emitter, Region, logical};

#[cfg(test)]
mod tests;

/// Keep speculative analysis and recursive rendering bounded, just like the
/// enclosing region emitter. Larger graphs remain ordinary control flow.
const MAX_NODES: usize = 128;

impl Emitter<'_> {
    /// The inner predicate assigns a local on the bypass edge. The other
    /// two edges enter one initializer, so Java's `||` definite-assignment
    /// rule expresses the join without copying the initializer or reading
    /// the assigned value along the short-circuited edge.
    pub(super) fn collapse_assigned_test<'a, 'c>(
        &mut self,
        head: usize,
        region: Region<'_, 'a, 'c>,
        machine: &mut Machine<'a, 'c>,
        condition: &mut Condition,
        offsets: &mut Vec<u32>,
        control: &mut RangeInclusive<u32>,
    ) -> Option<AssignedTest<'a, 'c>> {
        if !machine.stack_is_empty()
            || !machine.this_is_initialized()
            || region.exception_arm.is_some()
            || region.predicate.is_some()
            || !self.graph.blocks[head].exception_successors.is_empty()
        {
            return None;
        }
        let target = self.layout.normal_join(head, region)?;
        if region.post_test_latch() == Some(target)
            || target == condition.taken
            || target == condition.fallthrough
        {
            return None;
        }
        let (inner, missing) = [
            (condition.fallthrough, condition.taken),
            (condition.taken, condition.fallthrough),
        ]
        .into_iter()
        .find(|&(inner, missing)| {
            let test = &self.graph.blocks[inner];
            let shared = &self.graph.blocks[missing];
            test.successors.len() == 2
                && test.successors.contains(&target)
                && test.successors.contains(&missing)
                && shared.predecessors.len() == 2
                && shared.predecessors.contains(&head)
                && shared.predecessors.contains(&inner)
                && shared.exception_predecessors.is_empty()
                && !self.emitted[missing]
                && self.layout.inside(missing, region)
                && region.loop_transfer(missing).is_none()
                && self.decision_block_available(head, region, inner, *control.end(), |p| p == head)
        })?;
        let instructions = self.instructions;
        let instructions = &instructions[self.graph.blocks[inner].instructions.clone()];
        let [prefix @ .., dup, store, tail] = instructions else {
            return None;
        };
        let (slots, false) = store.local_access()? else {
            return None;
        };
        let slot = u16::try_from(slots.start).ok()?;
        if !matches!(dup.opcode, 0x59 | 0x5c)
            || !matches!(tail.opcode, 0x99..=0xa6 | 0xc6..=0xc7)
            || !prefix.iter().all(expression_op)
            || !self.local_is_live(target, slot)
        {
            return None;
        }
        let mut state = machine.switch_arm_entry(control).ok()?;
        let names = machine.local_name_checkpoint();
        let sites = machine.switch_anonymous_checkpoint();
        let result = (|| {
            let mut mapped = Vec::new();
            lift_test_prefix(prefix, &mut state, &mut mapped)?;
            let assignment = &instructions[prefix.len()..prefix.len() + 2];
            let step = state.step_assignment(assignment, |_, _| true).ok()??;
            let declaration = step.declaration?;
            if step.consumed != 2
                || !matches!(step.effect, Effect::None)
                || !state.take_prelude().is_empty()
            {
                return None;
            }
            let Effect::Branch { target, when_true, when_false } = state.step(tail).ok()? else {
                return None;
            };
            if !state.stack_is_empty()
                || !machine.has_fresh_test_local(&state, slot)
                || !state.take_prelude().is_empty()
            {
                return None;
            }
            let (taken, _) = self.branch_targets(inner, target).ok()?;
            mapped.extend(store.offset..store.offset + store.len);
            mapped.extend(tail.offset..tail.offset + tail.len);
            let tests = if taken == missing {
                (when_true, when_false)
            } else {
                (when_false, when_true)
            };
            Some((declaration, mapped, tests))
        })();
        let Some((declaration, mapped, (inner_missing, inner_assigned))) = result else {
            machine.restore_local_names(names);
            machine.restore_switch_anonymous_sites(sites);
            return None;
        };
        let (direct_missing, evaluates) = if condition.taken == missing {
            (&mut condition.when_true, &mut condition.when_false)
        } else {
            (&mut condition.when_false, &mut condition.when_true)
        };
        *condition = Condition {
            taken: target,
            fallthrough: missing,
            when_true: logical(std::mem::take(evaluates), "&&", inner_assigned),
            when_false: logical(std::mem::take(direct_missing), "||", inner_missing),
        };
        self.emitted[inner] = true;
        offsets.extend(mapped);
        *control = *control.start()..=tail.offset;
        machine.commit_switch_dynamic_helpers(&state);
        Some(AssignedTest { target, state, declaration, slot })
    }

    pub(super) fn collapse_decision_graph<'a, 'c>(
        &mut self,
        head: usize,
        region: Region<'_, 'a, 'c>,
        machine: &Machine<'a, 'c>,
        condition: &mut Condition,
        offsets: &mut Vec<u32>,
        control: &mut RangeInclusive<u32>,
    ) {
        if machine.has_uninitialized_stack() || condition.taken == condition.fallthrough {
            return;
        }
        let Some(mut owned) = self.decision_prefix(head, *control.end()) else {
            return;
        };
        loop {
            let empty = BTreeMap::new();
            if owned.len() == MAX_NODES
                || [condition.taken, condition.fallthrough]
                    .into_iter()
                    .all(|block| !self.decision_block(head, region, block, &owned, &empty, *control.end()))
            {
                return;
            }
            let mut baseline = machine.clone();
            let Ok(entry) = baseline.switch_arm_entry(control) else {
                return;
            };
            let names = machine.local_name_checkpoint();
            let sites = machine.switch_anonymous_checkpoint();
            let result = self.decision_frontier(head, region, condition, &entry, &owned, control);
            let Some(fold) = result else {
                machine.restore_local_names(names);
                machine.restore_switch_anonymous_sites(sites);
                return;
            };
            machine.commit_switch_dynamic_helpers(&entry);
            for block in fold.blocks {
                self.emitted[block] = true;
                owned.insert(block);
            }
            *condition = fold.condition;
            *control = *control.start()..=fold.end;
            offsets.extend(fold.offsets);
        }
    }

    /// The older short-circuit fold only follows a unique predecessor. Its
    /// control range ends at the last branch, so recover exactly that chain,
    /// not unrelated blocks which happen to have been emitted in the range.
    fn decision_prefix(&self, head: usize, end: u32) -> Option<BTreeSet<usize>> {
        let mut owned = BTreeSet::from([head]);
        if self.instructions[self.graph.blocks[head].instructions.end - 1].offset == end {
            return Some(owned);
        }
        let mut block = self.graph.blocks.partition_point(|node| {
            self.instructions[node.instructions.end - 1].offset < end
        });
        if self.instructions[self.graph.blocks.get(block)?.instructions.end - 1].offset != end {
            return None;
        }
        while block != head {
            let node = self.graph.blocks.get(block)?;
            if !self.emitted[block]
                || !node.exception_predecessors.is_empty()
                || node.exception_successors != self.graph.blocks[head].exception_successors
                || !owned.insert(block)
                || owned.len() > MAX_NODES
            {
                return None;
            }
            let &[predecessor] = node.predecessors.as_slice() else {
                return None;
            };
            block = predecessor;
        }
        Some(owned)
    }

    fn decision_frontier<'a, 'c>(
        &self,
        head: usize,
        region: Region<'_, 'a, 'c>,
        condition: &Condition,
        entry: &Machine<'a, 'c>,
        owned: &BTreeSet<usize>,
        control: &RangeInclusive<u32>,
    ) -> Option<Fold> {
        let mut frontier = BTreeSet::from([condition.taken, condition.fallthrough]);
        let mut decisions = BTreeMap::new();
        let mut offsets = Vec::new();
        let mut tested = 0;
        let mut end = *control.end();

        // In bytecode order, stop at the first two-way cut. In particular this
        // leaves a shared *next predicate* as a frontier, rather than copying
        // it into both arms of an outer ternary.
        while owned.len() + decisions.len() < MAX_NODES {
            let next = frontier.iter().copied().find(|&next| {
                !decisions.contains_key(&next)
                    && self.decision_block(head, region, next, owned, &decisions, *control.end())
            })?;
            let (decision, mapped, last) = self.lift_decision(next, entry)?;
            frontier.remove(&next);
            match &decision {
                Decision::Pass(target) => {
                    frontier.insert(*target);
                }
                Decision::Test(test) => {
                    tested += 1;
                    frontier.extend([test.taken, test.fallthrough]);
                }
            }
            decisions.insert(next, decision);
            offsets.extend(mapped);
            end = end.max(last);
            if tested == 0 || frontier.len() != 2 {
                continue;
            }
            let mut leaves = frontier.iter().copied();
            let [first, second] = [leaves.next()?, leaves.next()?];
            let mut expression = Expression {
                decisions: &decisions,
                used: BTreeSet::new(),
            };
            let [when_false, when_true] = expression.test(condition, [first, second])?;
            if expression.used.len() != tested {
                return None;
            }
            return Some(Fold {
                condition: Condition {
                    taken: second,
                    fallthrough: first,
                    when_true,
                    when_false,
                },
                blocks: decisions.into_keys().collect(),
                offsets,
                end,
            });
        }
        None
    }

    fn decision_block(
        &self,
        head: usize,
        region: Region<'_, '_, '_>,
        block: usize,
        owned: &BTreeSet<usize>,
        decisions: &BTreeMap<usize, Decision>,
        last_test: u32,
    ) -> bool {
        if !self.decision_block_available(head, region, block, last_test, |p| {
            owned.contains(&p) || decisions.contains_key(&p)
        }) {
            return false;
        }
        let ops = &self.instructions[self.graph.blocks[block].instructions.clone()];
        match self.graph.blocks[block].successors.len() {
            1 => matches!(ops, [op]
                if matches!(op.opcode, 0xa7 | 0xc8) && matches!(op.operand, Operand::Branch(_))),
            2 => ops.split_last().is_some_and(|(tail, expression)| {
                matches!(tail.opcode, 0x99..=0xa6 | 0xc6..=0xc7)
                    && expression.iter().all(expression_op)
            }),
            _ => false,
        }
    }

    fn decision_block_available(
        &self,
        head: usize,
        region: Region<'_, '_, '_>,
        block: usize,
        last_test: u32,
        owns: impl Fn(usize) -> bool,
    ) -> bool {
        let node = &self.graph.blocks[block];
        !(self.offset(block) <= last_test
            || self.emitted[block]
            || self.assertion_starts(block)
            || self.layout.loops[block].is_some()
            || !self.layout.inside(block, region)
            || region.loop_transfer(block).is_some()
            || !self.exceptions.contains(region.exception_arm, block)
            || self.exceptions.at_start(region.exception_arm, block).is_some()
            || self.exceptions.skips_binding(block)
            || self.exceptions.cleanup_prefix(block) != 0
            || self.exceptions.monitor_acquisition_end(block).is_some()
            || self.exceptions.finally_range(region.exception_arm, block).is_some()
            || self.exceptions.return_split(region.exception_arm, block).is_some()
            || self.exception_redirects.contains_key(&block)
            || self.exceptions.bypass_cleanup(block) != block
            || !node.exception_predecessors.is_empty()
            || node.exception_successors != self.graph.blocks[head].exception_successors
            || node.predecessors.iter().any(|&p| !owns(p))
            || node.successors.iter().any(|&target| target <= block)
            || node.instructions.clone().any(|index| {
                self.exceptions.skips_instruction(index) || region.for_loop_omits(index)
            }))
    }

    fn lift_decision(
        &self,
        block: usize,
        entry: &Machine<'_, '_>,
    ) -> Option<(Decision, Vec<u32>, u32)> {
        let node = &self.graph.blocks[block];
        let (tail, expression) = self.instructions[node.instructions.clone()].split_last()?;
        if let &[target] = node.successors.as_slice() {
            return Some((Decision::Pass(target), Vec::new(), tail.offset));
        }
        // An empty operand stack above the enclosing prefix proves that the
        // predicate is independent of it (even dup/pop cannot borrow from it).
        let mut trial = entry.clone();
        let mut offsets = Vec::new();
        lift_test_prefix(expression, &mut trial, &mut offsets)?;
        let Effect::Branch {
            target,
            when_true,
            when_false,
        } = trial.step(tail).ok()?
        else {
            return None;
        };
        if !trial.stack_is_empty() || !trial.same_locals(entry) || !trial.take_prelude().is_empty() {
            return None;
        }
        let (taken, fallthrough) = self.branch_targets(block, target).ok()?;
        offsets.extend(tail.offset..tail.offset + tail.len);
        Some((
            Decision::Test(Condition {
                taken,
                fallthrough,
                when_true,
                when_false,
            }),
            offsets,
            tail.offset,
        ))
    }
}

pub(super) struct AssignedTest<'a, 'c> {
    pub(super) target: usize,
    pub(super) state: Machine<'a, 'c>,
    pub(super) declaration: Document,
    pub(super) slot: u16,
}

fn expression_op(op: &Instruction) -> bool {
    matches!(
        op.opcode,
        0x00..=0x35 | 0x59..=0x83 | 0x85..=0x98 | 0xb2 | 0xb4 | 0xb6..=0xbe
            | 0xc0..=0xc1 | 0xc5
    )
}

fn lift_test_prefix(
    expression: &[Instruction],
    trial: &mut Machine<'_, '_>,
    offsets: &mut Vec<u32>,
) -> Option<()> {
    for op in expression {
        if !matches!(trial.step(op).ok()?, Effect::None) || !trial.take_prelude().is_empty() {
            return None;
        }
        if trial.instruction_has_source() {
            offsets.extend(op.offset..op.offset + op.len);
        }
    }
    Some(())
}

struct Fold {
    condition: Condition,
    blocks: Vec<usize>,
    offsets: Vec<u32>,
    end: u32,
}

enum Decision {
    Pass(usize),
    Test(Condition),
}

struct Expression<'a> {
    decisions: &'a BTreeMap<usize, Decision>,
    used: BTreeSet<usize>,
}

impl Expression<'_> {
    /// Both orientations share the same graph traversal; the structurer may
    /// choose either outcome as the statement's then arm.
    fn test(&mut self, root: &Condition, leaves: [usize; 2]) -> Option<[Document; 2]> {
        let (mut yes, mut no) = (self.through(root.fallthrough), self.through(root.taken));
        let (mut when_yes, mut when_no) = (root.when_false.clone(), root.when_true.clone());
        // Factor a test whose other edge is the sibling route before visiting
        // either arm. That sibling can be another conditional, not just an
        // exit; it must not be copied into both sides of a ternary.
        loop {
            let mut fold = None;
            for (block, shared) in [(yes, no), (no, yes)] {
                if let Some(Decision::Test(inner)) = self.decisions.get(&block) {
                    let (inner_yes, inner_no) =
                        (self.through(inner.fallthrough), self.through(inner.taken));
                    if inner_no == shared {
                        fold = Some((block, inner_yes, &inner.when_false, &inner.when_true));
                        break;
                    }
                    if inner_yes == shared {
                        fold = Some((block, inner_no, &inner.when_true, &inner.when_false));
                        break;
                    }
                }
            }
            let Some((block, target, succeeds, fails)) = fold else {
                break;
            };
            if !self.used.insert(block) {
                return None;
            }
            if yes == block {
                yes = target;
                when_yes = logical(when_yes, "&&", succeeds.clone());
                when_no = logical(when_no, "||", fails.clone());
            } else {
                no = target;
                when_no = logical(when_no, "&&", succeeds.clone());
                when_yes = logical(when_yes, "||", fails.clone());
            }
        }
        if yes == no {
            // The test still evaluates, so this is not a constant expression.
            return None;
        }
        let yes = self.value(yes, leaves)?;
        let no = self.value(no, leaves)?;
        combine(when_yes, when_no, yes, no)
    }

    fn through(&self, mut block: usize) -> usize {
        while let Some(Decision::Pass(next)) = self.decisions.get(&block) {
            block = *next;
        }
        block
    }

    fn value(&mut self, block: usize, leaves: [usize; 2]) -> Option<Value> {
        let decisions = self.decisions;
        match decisions.get(&block) {
            Some(Decision::Test(test)) => {
                if !self.used.insert(block) {
                    return None;
                }
                Some(Value::Test(self.test(test, leaves)?))
            }
            None if block == leaves[0] => Some(Value::Exit(true)),
            None if block == leaves[1] => Some(Value::Exit(false)),
            None => None,
            Some(Decision::Pass(_)) => unreachable!("pass-throughs are resolved before rendering"),
        }
    }
}

enum Value {
    Exit(bool),
    Test([Document; 2]),
}

/// An exit is true iff it reaches the first outcome. Use short-circuit
/// operators instead of spelling either boolean constant explicitly.
fn combine(yes: Document, no: Document, when_yes: Value, when_no: Value) -> Option<[Document; 2]> {
    Some(match (when_yes, when_no) {
        (Value::Exit(true), Value::Exit(false)) => [yes, no],
        (Value::Exit(false), Value::Exit(true)) => [no, yes],
        (Value::Exit(true), Value::Test([a, b])) => [logical(yes, "||", a), logical(no, "&&", b)],
        (Value::Exit(false), Value::Test([a, b])) => [logical(no, "&&", a), logical(yes, "||", b)],
        (Value::Test([a, b]), Value::Exit(true)) => [logical(no, "||", a), logical(yes, "&&", b)],
        (Value::Test([a, b]), Value::Exit(false)) => [logical(yes, "&&", a), logical(no, "||", b)],
        (Value::Test([a, b]), Value::Test([c, d])) => {
            let parens = yes.infix() == Some(Infix::TERNARY);
            let select = |when_yes, when_no| Document::ternary_expression([&yes, when_yes, when_no], parens);
            [select(&a, &c), select(&b, &d)]
        }
        (Value::Exit(_), Value::Exit(_)) => return None,
    })
}
