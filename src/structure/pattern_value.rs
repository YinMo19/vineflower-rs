// Pattern arms share ordinary switch-expression ownership and rendering.

use std::ops::RangeInclusive;

use crate::{lift::Machine, source_text::Document};

use super::{Arm, Emitter, Region};
use super::super::switch_expression::{DefaultLabel, Rule, RuleResult, SwitchExpression};

impl Emitter<'_> {
    pub(super) fn try_pattern_switch_value<'a, 'c>(
        &mut self,
        header: usize,
        region: Region<'_, 'a, 'c>,
        machine: &mut Machine<'a, 'c>,
        depth: usize,
        selector: &Document,
        arms: &[(usize, Arm)],
        staged: &[super::BoundArm<'a, 'c>],
        default: usize,
        join: usize,
        control: &RangeInclusive<u32>,
        constructor_setup: Option<usize>,
    ) -> bool {
        if !machine.supports_switch_expressions()
            || constructor_setup.is_none() && arms.iter().any(|(_, arm)| arm.guard.is_some())
        {
            return false;
        }
        if arms.iter().any(|(target, arm)| {
            *target == default && arm.keys.contains(&super::NULL_KEY) && !machine.supports_null_default()
        }) {
            return false;
        }
        let consumer_index = self.graph.blocks[join].instructions.start;
        let consumer = &self.instructions[consumer_index];
        if constructor_setup.is_some_and(|start| {
            !self.instructions.get(start..consumer_index)
                .is_some_and(|body| machine.proves_constructor_switch(body, consumer))
        }) {
            return false;
        }
        let entries = || arms.iter().map(|(target, arm)| arm.guard.as_ref().map_or(*target, |guard| guard.success));
        let Some(proof) = self.switch_region_entries(header, region, entries(), join, |entry, pred| {
            arms.iter().any(|(target, arm)| match &arm.guard {
                Some(guard) => guard.success == entry && guard.blocks().any(|owned| owned == pred),
                None => *target == entry && pred == header,
            })
        }) else {
            return false;
        };
        let names = machine.local_name_checkpoint();
        let anonymous = machine.switch_anonymous_checkpoint();
        let start = self.lines.len();
        let arm_region = region.switch_body(Some(join));
        let trial = (|| {
            let mut lifted = Vec::with_capacity(arms.len());
            let mut helpers = Vec::with_capacity(arms.len());
            for ((target, arm), bound) in arms.iter().zip(staged) {
                let mut local = bound.entry.clone();
                let entry = local.switch_arm_entry(control).ok()?;
                helpers.push(entry.clone());
                let path = if let Some(guard) = &arm.guard {
                    self.branch_arm(guard.success, arm_region, &entry, depth + 2).ok()?
                } else if let Some((indices, _)) = &arm.binding {
                    self.pattern_arm(*target, arm_region, entry, depth + 2, indices.end).ok()?
                } else {
                    self.branch_arm(*target, arm_region, &entry, depth + 2).ok()?
                };
                lifted.push(path);
            }
            if !proof.owners.keys().all(|&block| self.emitted[block]) {
                return None;
            }
            let normal: Vec<_> = lifted.iter().filter_map(|arm| arm.exit.as_ref()).collect();
            let mut value = if constructor_setup.is_some() {
                machine.join_constructor_switch_values(&normal, consumer, control, proof.last)?
            } else {
                machine.join_switch_values(&normal, control, proof.last).ok()??
            };
            let mut locals = machine.clone();
            let locals = locals.merge_locals(&normal, self.offset(join), |slot| self.local_is_live(join, slot)).ok()?;
            if !locals.declarations.is_empty() || locals.arms.iter().any(|arm| !arm.is_empty()) {
                return None;
            }
            let mut yields = std::mem::take(&mut value.yields).into_iter();
            let mut all_statements = self.lines.drain(start..);
            let rules = arms.iter().zip(staged).zip(lifted).map(|(((target, arm), bound), body)| {
                let statements: Vec<_> = all_statements.by_ref().take(body.end - body.start).collect();
                let result = if body.exit.is_some() {
                    RuleResult::Yield(yields.next().expect("normal rule has a yield"))
                } else {
                    RuleResult::Abrupt {
                        inline_throw: statements.len() == 1 && self.graph.blocks[*target].successors.is_empty(),
                    }
                };
                Rule {
                    labels: &bound.labels,
                    default: if *target != default { DefaultLabel::Absent }
                        else if arm.keys.contains(&super::NULL_KEY) { DefaultLabel::NullDefault }
                        else { DefaultLabel::Default },
                    statements,
                    trailing_offsets: body.offsets,
                    result,
                }
            }).collect();
            drop(all_statements);
            machine.push_switch_value(value, SwitchExpression { selector, rules, depth }.render()).ok()?;
            Some(helpers)
        })();
        if let Some(helpers) = trial {
            for helper in &helpers {
                machine.commit_switch_dynamic_helpers(helper);
            }
            return true;
        }
        self.lines.truncate(start);
        for block in proof.owners.into_keys() {
            self.emitted[block] = false;
        }
        machine.restore_local_names(names);
        machine.restore_switch_anonymous_sites(anonymous);
        false
    }
}
