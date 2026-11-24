use std::{collections::{BTreeMap, BTreeSet}, ops::{Range, RangeInclusive}};

use crate::lift::{Effect, Machine};

use super::{
    AssignedTest, Condition, Decision, Emitter, Expression, MAX_NODES, Region,
    has_test_assignment, lift_test_assignment, lift_test_prefix,
};

const BEFORE: u8 = 1;
const ASSIGNED: u8 = 2;

type Local<'a, 'c> = (AssignedTest<'a, 'c>, Range<u32>);

impl Emitter<'_> {
    pub(super) fn collapse_assigned_decisions<'a, 'c>(
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
            let owned = BTreeSet::from([head]);
            let mut frontier = BTreeSet::from([condition.taken, condition.fallthrough]);
            let mut decisions = BTreeMap::new();
            let mut reaching = BTreeMap::from([(head, BEFORE)]);
            let mut local = None;
            let mut mapped = Vec::new();
            let mut tested = 0;
            let mut end = *control.end();
            while reaching.len() < MAX_NODES {
                let block = frontier.iter().copied().find(|&block| {
                    block != join
                        && self.decision_block(head, region, block, &owned, &decisions, *control.end())
                })?;
                let node = &self.graph.blocks[block];
                let incoming = incoming_paths(&node.predecessors, &reaching)?;
                let (decision, outgoing) = self.lift_assigned_decision(
                    block, &entry, incoming, &mut local, &mut mapped,
                )?;
                tested += usize::from(matches!(decision, Decision::Test(_)));
                end = end.max(self.instructions[node.instructions.end - 1].offset);
                frontier.remove(&block);
                frontier.extend(&node.successors);
                reaching.insert(block, outgoing);
                decisions.insert(block, decision);

                if frontier.len() != 2 || local.is_none() || frontier.iter().any(|&leaf| {
                    let node = &self.graph.blocks[leaf];
                    self.emitted[leaf] || !self.layout.inside(leaf, region)
                        || !node.exception_predecessors.is_empty()
                        || incoming_paths(&node.predecessors, &reaching) != Some(ASSIGNED)
                }) {
                    continue;
                }
                // Each successor can consume the new local only once every
                // path to it executes a store in the reconstructed expression.
                let mut leaves = frontier.into_iter();
                let [first, second] = [leaves.next()?, leaves.next()?];
                let mut expression = Expression { decisions: &decisions, used: BTreeSet::new() };
                let [when_false, when_true] = expression.test(condition, [first, second])?;
                if expression.used.len() != tested {
                    return None;
                }
                let (mut test, _) = local?;
                test.state.finish_predicate_local(test.slot, [self.offset(first), self.offset(second)]);
                return Some((test, Condition {
                    taken: second, fallthrough: first, when_true, when_false,
                }, decisions, mapped, end));
            }
            None
        })();
        let Some((mut test, folded, decisions, mapped, end)) = result else {
            machine.restore_local_names(names);
            machine.restore_switch_anonymous_sites(sites);
            return None;
        };
        for block in decisions.into_keys() {
            self.emitted[block] = true;
        }
        *condition = folded;
        *control = *control.start()..=end;
        offsets.extend(mapped);
        machine.commit_predicate_state(&mut test.state);
        Some(test)
    }

    fn lift_assigned_decision<'a, 'c>(
        &self,
        block: usize,
        entry: &Machine<'a, 'c>,
        mut incoming: u8,
        local: &mut Option<Local<'a, 'c>>,
        offsets: &mut Vec<u32>,
    ) -> Option<(Decision, u8)> {
        let node = &self.graph.blocks[block];
        if let &[target] = node.successors.as_slice() {
            return Some((Decision::Pass(target), incoming));
        }
        let (tail, prefix) = self.instructions[node.instructions.clone()].split_last()?;
        let mut trial = entry.clone();
        if let Some((test, slots)) = local.as_ref() {
            if incoming == ASSIGNED {
                trial.prefer_test_local(&test.state, test.slot);
            } else if incoming != BEFORE {
                // A shared predicate sees different reaching definitions.
                // It is safe to lift against the old state only when an
                // independent store replaces the local before any read.
                for (accessed, read) in prefix.iter().filter_map(|op| op.local_access()) {
                    if accessed.start < slots.end && slots.start < accessed.end {
                        if read || accessed != *slots {
                            return None;
                        }
                        break;
                    }
                }
            }
        }
        lift_test_prefix(prefix, &mut trial, offsets, |trial, pair, slot| {
            if let Some((test, _)) = local.as_ref() {
                if slot != test.slot {
                    return None;
                }
                trial.use_predicate_store_binding(&test.state, &pair[1], slot)?;
                if lift_test_assignment(trial, pair)?.is_some() {
                    return None;
                }
                trial.prefer_test_local(&test.state, slot);
            } else {
                let declaration = lift_test_assignment(trial, pair)??;
                if !entry.has_only_predicate_local(trial, slot) {
                    return None;
                }
                let mut state = entry.clone();
                state.prefer_test_local(trial, slot);
                let (slots, _) = pair[1].local_access()?;
                *local = Some((AssignedTest { target: None, state, declaration, slot }, slots));
            }
            incoming = ASSIGNED;
            Some(())
        })?;
        let Effect::Branch { target, when_true, when_false } = trial.step(tail).ok()? else {
            return None;
        };
        let state = if incoming == ASSIGNED { &local.as_ref()?.0.state } else { entry };
        if !trial.stack_is_empty() || !trial.same_locals(state) || !trial.take_prelude().is_empty() {
            return None;
        }
        let (taken, fallthrough) = self.branch_targets(block, target).ok()?;
        offsets.extend(tail.offset..tail.offset + tail.len);
        Some((Decision::Test(Condition { taken, fallthrough, when_true, when_false }), incoming))
    }
}

fn incoming_paths(predecessors: &[usize], reaching: &BTreeMap<usize, u8>) -> Option<u8> {
    predecessors.iter().try_fold(0, |paths, predecessor| Some(paths | *reaching.get(predecessor)?))
}
