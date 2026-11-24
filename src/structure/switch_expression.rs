// Based on Vineflower SwitchExpressionHelper (Apache-2.0).

use std::{
    collections::{BTreeMap, btree_map::Entry},
    ops::RangeInclusive,
};

use crate::lift::Machine;

use super::{Emitter, Line, flow::Region};

pub(super) struct CaseLabel {
    pub(super) text: String,
    pub(super) offsets: Vec<u32>,
}

struct SwitchRegion {
    owners: BTreeMap<usize, usize>,
    last: u32,
}

struct Rule<'a> {
    labels: &'a [CaseLabel],
    default: bool,
    statements: Vec<Line>,
    trailing_offsets: Vec<u32>,
    result: RuleResult,
}

enum RuleResult {
    Yield(String),
    Abrupt { inline_throw: bool },
}

struct SwitchExpression<'a> {
    selector: &'a str,
    rules: Vec<Rule<'a>>,
}

impl Emitter<'_> {
    pub(super) fn try_switch_expression<'a, 'c>(
        &mut self,
        header: usize,
        region: Region<'_, 'a, 'c>,
        machine: &mut Machine<'a, 'c>,
        depth: usize,
        selector: &str,
        groups: &BTreeMap<usize, Vec<CaseLabel>>,
        default: usize,
        join: usize,
        offsets: &mut Vec<u32>,
        control: &RangeInclusive<u32>,
    ) -> bool {
        if !machine.supports_switch_expressions() {
            return false;
        }
        let Some(proof) = self.switch_region(header, region, groups, join) else {
            return false;
        };
        let Ok(mut entry) = machine.switch_arm_entry(control) else {
            return false;
        };
        let names = machine.local_name_checkpoint();
        let anonymous = machine.switch_anonymous_checkpoint();
        let start = self.lines.len();
        let arm_region = region.switch_body(Some(join));
        let recovered = (|| {
            let mut arms = Vec::with_capacity(groups.len());
            for &target in groups.keys() {
                arms.push(
                    self.branch_arm(target, arm_region, &entry, depth + 2)
                        .ok()?,
                );
            }
            if !proof.owners.keys().all(|&block| self.emitted[block]) {
                return None;
            }
            let normal = arms
                .iter()
                .filter_map(|arm| arm.exit.as_ref())
                .collect::<Vec<_>>();
            let mut value = machine
                .join_switch_values(&normal, control, proof.last)
                .ok()??;
            // A yield can retain assignments to existing visible bindings. It
            // cannot export a declaration or introduce parallel copies for the
            // continuation, since those bindings would escape the rule scope.
            let locals = entry
                .merge_locals(&normal, self.offset(join), |slot| {
                    self.local_is_live(join, slot)
                })
                .ok()?;
            if !locals.declarations.is_empty() || locals.arms.iter().any(|arm| !arm.is_empty()) {
                return None;
            }
            let mut yields = std::mem::take(&mut value.yields).into_iter();
            let mut statements = self.lines.drain(start..);
            let rules = groups
                .iter()
                .zip(arms)
                .map(|((&target, labels), arm)| {
                    let statements = statements
                        .by_ref()
                        .take(arm.end - arm.start)
                        .collect::<Vec<_>>();
                    let result = if arm.exit.is_some() {
                        RuleResult::Yield(yields.next().expect("one value per normal arm"))
                    } else {
                        // A one-block abrupt arm was proven to end in athrow;
                        // single-statement lifting gives exactly the throw rule.
                        let inline = statements.len() == 1
                            && self.graph.blocks[target].successors.is_empty();
                        RuleResult::Abrupt {
                            inline_throw: inline,
                        }
                    };
                    Rule {
                        labels,
                        default: target == default,
                        statements,
                        trailing_offsets: arm.offsets,
                        result,
                    }
                })
                .collect();
            let expression = SwitchExpression { selector, rules };
            let (text, mapped) = expression.inline();
            machine.push_switch_value(value, text).ok()?;
            Some(mapped)
        })();
        if let Some(mapped) = recovered {
            machine.commit_switch_dynamic_helpers(&entry);
            offsets.extend(mapped);
            return true;
        }

        // Arm lifting is a transaction. It can allocate Java names or
        // register nested constructions even if it cannot prove a result.
        self.lines.truncate(start);
        for block in proof.owners.into_keys() {
            self.emitted[block] = false;
        }
        machine.restore_local_names(names);
        machine.restore_switch_anonymous_sites(anonymous);
        false
    }

    fn switch_region(
        &self,
        header: usize,
        region: Region<'_, '_, '_>,
        groups: &BTreeMap<usize, Vec<CaseLabel>>,
        join: usize,
    ) -> Option<SwitchRegion> {
        if join <= header
            || self.emitted[join]
            || groups.contains_key(&join)
            || region.loop_transfer(join).is_some()
        {
            return None;
        }
        let switch_region = region.switch_body(Some(join));
        let blocks = &self.graph.blocks;
        if !blocks[join].exception_predecessors.is_empty()
            || blocks[join].exception_successors != blocks[header].exception_successors
            || groups
                .keys()
                .any(|&target| !self.layout.inside(target, switch_region))
        {
            return None;
        }
        let mut owners = BTreeMap::new();
        let mut pending = Vec::new();
        let mut reaches_join = false;
        let mut last = self.offset(header);
        for &target in groups.keys() {
            pending.push(target);
            while let Some(block) = pending.pop() {
                match owners.entry(block) {
                    Entry::Occupied(owner) if *owner.get() == target => continue,
                    Entry::Occupied(_) => return None,
                    Entry::Vacant(owner) => {
                        owner.insert(target);
                    }
                }
                let body = &blocks[block];
                if !(header < block && block < join)
                    || self.emitted[block]
                    || region.loop_transfer(block).is_some()
                    || !self.exceptions.contains(region.exception_arm, block)
                    || self
                        .exceptions
                        .at_start(region.exception_arm, block)
                        .is_some()
                    || !body.exception_predecessors.is_empty()
                    || body.exception_successors != blocks[header].exception_successors
                {
                    return None;
                }
                let tail = &self.instructions[body.instructions.end - 1];
                last = last.max(tail.offset);
                if body.successors.is_empty() && tail.opcode != 0xbf {
                    // A Java rule can throw, but cannot return from the
                    // containing method or transfer to its enclosing region.
                    return None;
                }
                for &next in &body.successors {
                    if next == join {
                        reaches_join = true;
                    } else {
                        pending.push(next);
                    }
                }
            }
        }
        if !reaches_join
            || owners.iter().any(|(&block, &owner)| {
                blocks[block].predecessors.iter().any(|pred| {
                    (*pred != header || block != owner) && owners.get(pred) != Some(&owner)
                })
            })
            || (region.stop != Some(join)
                && blocks[join]
                    .predecessors
                    .iter()
                    .any(|pred| !owners.contains_key(pred)))
        {
            return None;
        }
        Some(SwitchRegion { owners, last })
    }
}

impl SwitchExpression<'_> {
    /// Compose the proven rules as one expression using the existing inline
    /// expression renderer, without dropping the individual rule mappings.
    fn inline(self) -> (String, Vec<u32>) {
        let mut text = format!("switch ({}) {{", self.selector);
        let mut offsets = Vec::new();
        for Rule {
            labels,
            default,
            statements,
            trailing_offsets,
            result,
        } in self.rules
        {
            if default {
                text.push_str(" default -> ");
                // Explicit labels sharing this target are already covered
                // by default; Java does not allow `case k, default`.
                offsets.extend(
                    labels
                        .iter()
                        .flat_map(|label| label.offsets.iter().copied()),
                );
            } else {
                text.push_str(" case ");
                for (i, label) in labels.iter().enumerate() {
                    if i != 0 {
                        text.push_str(", ");
                    }
                    text.push_str(&label.text);
                    offsets.extend_from_slice(&label.offsets);
                }
                text.push_str(" -> ");
            }
            let block = match &result {
                RuleResult::Yield(_) => !statements.is_empty(),
                RuleResult::Abrupt { inline_throw } => !inline_throw,
            };
            if block {
                text.push('{');
            }
            for (i, line) in statements.into_iter().enumerate() {
                if block || i != 0 {
                    text.push(' ');
                }
                text.push_str(&line.text);
                offsets.extend(line.offsets);
            }
            if let RuleResult::Yield(value) = result {
                if block {
                    text.push_str(" yield ");
                }
                text.push_str(&value);
                text.push(';');
            }
            offsets.extend(trailing_offsets);
            if block {
                text.push_str(" }");
            }
        }
        text.push_str(" }");
        (text, offsets)
    }
}

#[cfg(test)]
#[path = "switch_expression_tests.rs"]
mod tests;
