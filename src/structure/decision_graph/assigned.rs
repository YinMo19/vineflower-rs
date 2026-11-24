use std::{collections::{BTreeMap, BTreeSet}, ops::{Range, RangeInclusive}};

use crate::lift::{Effect, Machine};
use crate::source_text::Document;

use super::{
    AssignedTest, Condition, Decision, Emitter, Expression, MAX_NODES, Region, TestBinding,
    has_test_assignment, lift_test_assignment, lift_test_prefix,
};

/// The tracked declarations have bounded, dense indices, not JVM slot indices.
/// A bit in `some` but not `every` marks an ambiguous reaching definition.
#[derive(Clone, Copy, Default)]
struct Reaching {
    some: u64,
    every: u64,
}

impl Reaching {
    fn assign(&mut self, index: usize) {
        self.some |= 1 << index;
        self.every |= 1 << index;
    }

    fn merge(self, other: Self) -> Self {
        Self { some: self.some | other.some, every: self.every & other.every }
    }
}

struct TestLocal {
    slots: Range<u32>,
    declaration: Document,
}

impl TestLocal {
    fn slot(&self) -> u16 {
        self.slots.start as u16
    }
}

impl Emitter<'_> {
    /// Recognize the two constant-producing blocks of a stack-valued test.
    /// A fresh local can belong entirely to that test, not to either arm.
    pub(super) fn assigned_value_leaves(
        &self,
        head: usize,
        region: Region<'_, '_, '_>,
    ) -> Option<[usize; 2]> {
        let join = self.layout.normal_join(head, region)?;
        let &[a, b] = self.graph.blocks[join].predecessors.as_slice() else { return None };
        let value = |block: usize| {
            let node = &self.graph.blocks[block];
            if node.successors.as_slice() != [join]
                || region.loop_transfer(block).is_some()
                || self.layout.loops[block].is_some()
            {
                return None;
            }
            let [constant, rest @ ..] = &self.instructions[node.instructions.clone()] else {
                return None;
            };
            (matches!(constant.opcode, 0x03 | 0x04)
                && (rest.is_empty() || matches!(rest, [jump] if matches!(jump.opcode, 0xa7 | 0xc8))))
                .then_some(constant.opcode)
        };
        (value(a)? != value(b)?).then_some([a.min(b), a.max(b)])
    }

    pub(super) fn collapse_assigned_decisions<'a, 'c>(
        &mut self,
        head: usize,
        region: Region<'_, 'a, 'c>,
        machine: &mut Machine<'a, 'c>,
        condition: &mut Condition,
        offsets: &mut Vec<u32>,
        control: &mut RangeInclusive<u32>,
        value_leaves: Option<[usize; 2]>,
    ) -> Option<AssignedTest<'a, 'c>> {
        if !machine.stack_is_empty()
            || !machine.this_is_initialized()
            || region.exception_arm.is_some()
            || region.protected.is_some()
            || region.predicate.is_some()
            || !self.graph.blocks[head].exception_successors.is_empty()
            || ![condition.fallthrough, condition.taken].into_iter().any(|block| {
                has_test_assignment(&self.instructions[self.graph.blocks[block].instructions.clone()])
            })
        {
            return None;
        }
        let join = self.layout.normal_join(head, region)?;
        let entry = machine.switch_arm_entry(control).ok()?;
        let names = machine.local_name_checkpoint();
        let sites = machine.switch_anonymous_checkpoint();
        let result = (|| {
            let mut owned = BTreeSet::from([head]);
            let mut frontier = BTreeSet::from([condition.taken, condition.fallthrough]);
            let mut decisions = BTreeMap::new();
            let mut reaching = BTreeMap::from([(head, Reaching::default())]);
            let mut canonical = entry.clone();
            let mut locals = Vec::new();
            let mut mapped = Vec::new();
            let mut staged = None;
            let mut tested = 0;
            let mut end = *control.end();
            while reaching.len() < MAX_NODES {
                let block = frontier.iter().copied().find(|&block| {
                    block != join && !value_leaves.is_some_and(|leaves| leaves.contains(&block))
                        && self.decision_block(head, region, block, &owned, &decisions, *control.end())
                })?;
                let node = &self.graph.blocks[block];
                let incoming = incoming_paths(node.predecessors.iter().copied(), &reaching)?;
                let (decision, outgoing) = self.lift_assigned_decision(
                    block, (&entry, &mut canonical), incoming, &mut locals, &mut mapped,
                    value_leaves.is_some(),
                )?;
                tested += usize::from(matches!(decision, Decision::Test(_)));
                end = end.max(self.instructions[node.instructions.end - 1].offset);
                frontier.remove(&block);
                frontier.extend(&node.successors);
                reaching.insert(block, outgoing);
                decisions.insert(block, decision);

                if locals.is_empty() || frontier.len() != 2 {
                    continue;
                }
                let mut leaves = frontier.iter().copied();
                let leaves = [leaves.next()?, leaves.next()?];
                let source = staged.as_ref().unwrap_or(condition);
                if let Some(masks) = self.assigned_exit_masks(
                    leaves, join, region, &reaching, &locals, &entry, value_leaves,
                ) {
                    let folded = render_cut(source, &decisions, leaves, tested)?;
                    for (index, local) in locals.iter().enumerate() {
                        let relevant = [masks[0] & (1 << index) != 0, masks[1] & (1 << index) != 0];
                        let binding_leaves = match relevant {
                            [true, true] => leaves,
                            [true, false] => [leaves[0]; 2],
                            [false, true] => [leaves[1]; 2],
                            [false, false] => continue,
                        };
                        canonical.finish_predicate_local(local.slot(), binding_leaves.map(|block| self.offset(block)));
                    }
                    let test = prepare_test(&entry, canonical, locals, leaves, masks)?;
                    owned.remove(&head);
                    owned.extend(decisions.into_keys());
                    return Some((test, folded, owned, mapped, end));
                }

                // On a fully owned two-way cut, factor shared *next tests*
                // before traversing either of them. Keep their individual
                // reaching states, including assignments correlated with
                // the truth value of this intermediate expression.
                if value_leaves.is_none()
                    && !leaves.contains(&source.taken)
                    && !leaves.contains(&source.fallthrough)
                    && leaves.iter().all(|&leaf| {
                        let preds = &self.graph.blocks[leaf].predecessors;
                        preds.len() > 1 && preds.iter().all(|pred| reaching.contains_key(pred))
                    })
                    && let Some(cut) = render_cut(source, &decisions, leaves, tested)
                {
                    staged = Some(cut);
                    owned.extend(std::mem::take(&mut decisions).into_keys());
                    tested = 0;
                }
            }
            None
        })();
        let Some((mut test, folded, owned, mapped, end)) = result else {
            machine.restore_local_names(names);
            machine.restore_switch_anonymous_sites(sites);
            return None;
        };
        for block in owned {
            self.emitted[block] = true;
        }
        *condition = folded;
        *control = *control.start()..=end;
        offsets.extend(mapped);
        if let Some(primary) = &mut test.primary {
            machine.commit_predicate_state(&mut primary.state);
            if let Some(secondary) = &mut test.secondary {
                machine.commit_predicate_state(&mut secondary.state);
            }
        } else {
            machine.commit_switch_dynamic_helpers(&entry);
        }
        Some(test)
    }

    fn assigned_exit_masks(
        &mut self,
        leaves: [usize; 2],
        join: usize,
        region: Region<'_, '_, '_>,
        reaching: &BTreeMap<usize, Reaching>,
        locals: &[TestLocal],
        entry: &Machine<'_, '_>,
        value_leaves: Option<[usize; 2]>,
    ) -> Option<[u64; 2]> {
        let ordinary = leaves.map(|leaf| {
            let node = &self.graph.blocks[leaf];
            (!self.emitted[leaf] && self.layout.inside(leaf, region)
                && node.exception_predecessors.is_empty())
                .then(|| incoming_paths(node.predecessors.iter().copied(), reaching))
                .flatten()
                .map(|paths| paths.every)
        });
        let fresh = |local: &TestLocal| entry.predicate_slot_is_fresh(local.slot());
        if let Some(expected) = value_leaves {
            return (expected == leaves && ordinary.iter().all(Option::is_some)
                && locals.iter().all(fresh)
                && !leaves.into_iter().any(|leaf| {
                    locals.iter().any(|local| self.local_is_live(leaf, local.slot()))
                }))
                .then_some([0, 0]);
        }
        let all = u64::MAX >> (u64::BITS as usize - locals.len());
        if ordinary == [Some(all); 2] {
            return Some([all; 2]);
        }
        let continuation = leaves.iter().position(|&leaf| leaf == join)?;
        let arm_index = 1 - continuation;
        let arm = leaves[arm_index];
        if self.emitted[join]
            || !self.graph.blocks[join].exception_predecessors.is_empty()
            || region.post_test_latch() == Some(join)
            || region.loop_transfer(arm).is_some()
        {
            return None;
        }
        let mut masks = [0; 2];
        masks[arm_index] = ordinary[arm_index]?;
        if let [local] = locals {
            // The lexical join may bypass the store if no continuation
            // reads its value. Only the other edge can use this local.
            return (masks[arm_index] == all && fresh(local)
                && !self.local_is_live(join, local.slot()) && self.local_is_live(arm, local.slot()))
                .then_some(masks);
        }
        // The only unowned predecessor at the join may be the arm itself.
        // Its actual locals are checked separately when the arm is emitted.
        if self.graph.blocks[arm].successors.as_slice() != [join] {
            return None;
        }
        let preds = self.graph.blocks[join].predecessors.iter().copied().filter(|&p| p != arm);
        masks[continuation] = incoming_paths(preds, reaching)?.every;
        for (index, local) in locals.iter().enumerate() {
            for (leaf, mask) in leaves.into_iter().zip(masks) {
                if mask & (1 << index) == 0 && (!fresh(local) || self.local_is_live(leaf, local.slot())) {
                    return None;
                }
            }
        }
        Some(masks)
    }

    fn lift_assigned_decision<'a, 'c>(
        &self,
        block: usize,
        (entry, canonical): (&Machine<'a, 'c>, &mut Machine<'a, 'c>),
        mut incoming: Reaching,
        locals: &mut Vec<TestLocal>,
        offsets: &mut Vec<u32>,
        allows_existing_assignments: bool,
    ) -> Option<(Decision, Reaching)> {
        let node = &self.graph.blocks[block];
        if let &[target] = node.successors.as_slice() {
            return Some((Decision::Pass(target), incoming));
        }
        let (tail, prefix) = self.instructions[node.instructions.clone()].split_last()?;
        let mut trial = entry.clone();
        for (index, local) in locals.iter().enumerate() {
            if incoming.every & (1 << index) != 0 {
                trial.prefer_test_local(canonical, local.slot());
            } else if incoming.some & (1 << index) != 0 {
                // A shared predicate sees different reaching definitions.
                // Lift against the original state only until a proved
                // store replaces the local; reject any ambiguous read.
                if let Some((accessed, read)) = prefix.iter().filter_map(|op| op.local_access())
                    .find(|(accessed, _)| overlaps(accessed, &local.slots))
                    && (read || accessed != local.slots)
                {
                    return None;
                }
            }
        }
        lift_test_prefix(prefix, &mut trial, offsets, |trial, pair, slot| {
            let (slots, _) = pair[1].local_access()?;
            let index = if let Some(index) = locals.iter().position(|local| overlaps(&slots, &local.slots)) {
                if slots != locals[index].slots {
                    return None;
                }
                trial.use_predicate_store_binding(canonical, &pair[1], slot)?;
                if lift_test_assignment(trial, pair)?.is_some() {
                    return None;
                }
                trial.prefer_test_local(canonical, slot);
                index
            } else {
                let Some(declaration) = lift_test_assignment(trial, pair)? else {
                    return allows_existing_assignments.then_some(());
                };
                if locals.len() == u64::BITS as usize {
                    return None;
                }
                canonical.adopt_predicate_local(trial, slot)?;
                let index = locals.len();
                locals.push(TestLocal { slots, declaration });
                index
            };
            incoming.assign(index);
            Some(())
        })?;
        let Effect::Branch { target, when_true, when_false } = trial.step(tail).ok()? else {
            return None;
        };
        if !trial.stack_is_empty()
            || !trial.same_predicate_locals(entry, canonical, |slot| {
                locals.iter().enumerate().any(|(index, binding)| {
                    binding.slot() == slot && incoming.every & (1 << index) != 0
                })
            })
            || !trial.take_prelude().is_empty()
        {
            return None;
        }
        let (taken, fallthrough) = self.branch_targets(block, target).ok()?;
        offsets.extend(tail.offset..tail.offset + tail.len);
        Some((Decision::Test(Condition { taken, fallthrough, when_true, when_false }), incoming))
    }
}

fn overlaps(a: &Range<u32>, b: &Range<u32>) -> bool {
    a.start < b.end && b.start < a.end
}

fn incoming_paths(
    predecessors: impl IntoIterator<Item = usize>,
    reaching: &BTreeMap<usize, Reaching>,
) -> Option<Reaching> {
    let mut predecessors = predecessors.into_iter();
    let first = *reaching.get(&predecessors.next()?)?;
    predecessors.try_fold(first, |paths, predecessor| {
        Some(paths.merge(*reaching.get(&predecessor)?))
    })
}

fn render_cut(
    source: &Condition,
    decisions: &BTreeMap<usize, Decision>,
    [fallthrough, taken]: [usize; 2],
    tested: usize,
) -> Option<Condition> {
    let mut expression = Expression { decisions, used: BTreeSet::new() };
    let [when_false, when_true] = expression.test(source, [fallthrough, taken])?;
    (expression.used.len() == tested).then_some(Condition { taken, fallthrough, when_true, when_false })
}

fn prepare_test<'a, 'c>(
    entry: &Machine<'a, 'c>,
    canonical: Machine<'a, 'c>,
    locals: Vec<TestLocal>,
    leaves: [usize; 2],
    masks: [u64; 2],
) -> Option<AssignedTest<'a, 'c>> {
    let all = u64::MAX >> (u64::BITS as usize - locals.len());
    let build_binding = |target, state, mask: u64| {
        let mut slots = locals.iter().enumerate().filter(|(index, _)| mask & (1 << index) != 0)
            .map(|(_, local)| local.slot());
        Some(TestBinding { target, state, slot: slots.next()?, more: slots.collect() })
    };
    let project = |mask| {
        let mut state = entry.clone();
        for (index, local) in locals.iter().enumerate() {
            if mask & (1 << index) != 0 {
                state.prefer_test_local(&canonical, local.slot());
            }
        }
        state
    };
    let primary_index = usize::from(masks[1].count_ones() > masks[0].count_ones());
    let other = 1 - primary_index;
    let secondary = (masks[other] != 0 && masks[other] != masks[primary_index])
        .then(|| build_binding(Some(leaves[other]), project(masks[other]), masks[other]).map(Box::new))
        .flatten();
    let primary_mask = masks[primary_index];
    let primary = if primary_mask == 0 {
        None
    } else {
        let target = (masks[0] != masks[1]).then_some(leaves[primary_index]);
        let state = if primary_mask == all { canonical } else { project(primary_mask) };
        build_binding(target, state, primary_mask)
    };
    let mut declarations = locals.into_iter().map(|local| local.declaration);
    Some(AssignedTest {
        declaration: declarations.next()?,
        more: declarations.collect(),
        primary,
        secondary,
    })
}
