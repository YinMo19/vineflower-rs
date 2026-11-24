//! Fold a closed, expression-only JVM decision graph into a Java boolean.

use std::collections::{BTreeMap, BTreeSet};
use std::ops::RangeInclusive;

use crate::bytecode::Operand;
use crate::lift::{Effect, Machine};
use crate::source_text::Document;

use super::{Condition, Emitter, Region, logical};

#[cfg(test)]
mod tests;

/// Keep speculative analysis and recursive rendering bounded, just like the
/// enclosing region emitter. Larger graphs remain ordinary control flow.
const MAX_NODES: usize = 128;

impl Emitter<'_> {
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
        let node = &self.graph.blocks[block];
        if self.offset(block) <= last_test
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
            || node.predecessors.iter().any(|p| !owned.contains(p) && !decisions.contains_key(p))
            || node.successors.iter().any(|&target| target <= block)
            || node.instructions.clone().any(|index| {
                self.exceptions.skips_instruction(index) || region.for_loop_omits(index)
            })
        {
            return false;
        }
        let ops = &self.instructions[node.instructions.clone()];
        match node.successors.len() {
            1 => matches!(ops, [op]
                if matches!(op.opcode, 0xa7 | 0xc8) && matches!(op.operand, Operand::Branch(_))),
            2 => ops.split_last().is_some_and(|(tail, expression)| {
                matches!(tail.opcode, 0x99..=0xa6 | 0xc6..=0xc7)
                    && expression.iter().all(|op| {
                        matches!(
                            op.opcode,
                            0x00..=0x35 | 0x59..=0x83 | 0x85..=0x98 | 0xb2 | 0xb4
                                | 0xb6..=0xbe | 0xc0..=0xc1 | 0xc5
                        )
                    })
            }),
            _ => false,
        }
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
        for op in expression {
            if !matches!(trial.step(op).ok()?, Effect::None) || !trial.take_prelude().is_empty() {
                return None;
            }
            if trial.instruction_has_source() {
                offsets.extend(op.offset..op.offset + op.len);
            }
        }
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
            [ternary(yes.clone(), a, c), ternary(yes, b, d)]
        }
        (Value::Exit(_), Value::Exit(_)) => return None,
    })
}

fn ternary(mut selector: Document, mut yes: Document, mut no: Document) -> Document {
    for value in [&mut selector, &mut yes, &mut no] {
        if value.contains('?') {
            value.surround("(", ")");
        }
    }
    selector.push_str(" ? ");
    selector.append(yes);
    selector.push_str(" : ");
    selector.append(no);
    selector
}
