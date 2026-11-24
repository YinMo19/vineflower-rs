// Based on Vineflower SwitchExpressionHelper (Apache-2.0).

use std::{
    collections::{BTreeMap, BTreeSet, btree_map::Entry},
    ops::RangeInclusive,
};

use crate::{
    bytecode::Operand,
    lift::{Effect, Machine},
    source_text::Document,
};

use super::{Condition, Emitter, Line, Tail, flow::Region, surrounded};

pub(super) mod predicate;

pub(super) struct CaseLabel {
    pub(super) text: Document,
    pub(super) offsets: Vec<u32>,
}

pub(super) struct SwitchRegion {
    pub(super) owners: BTreeMap<usize, usize>,
    pub(super) last: u32,
}

pub(super) struct Rule<'a> {
    pub(super) labels: &'a [CaseLabel],
    pub(super) default: DefaultLabel,
    pub(super) statements: Vec<Line>,
    pub(super) trailing_offsets: Vec<u32>,
    pub(super) result: RuleResult,
}

#[derive(Clone, Copy)]
pub(super) enum DefaultLabel {
    Absent,
    Default,
    NullDefault,
}

impl From<bool> for DefaultLabel {
    fn from(value: bool) -> Self {
        if value {
            Self::Default
        } else {
            Self::Absent
        }
    }
}

pub(super) enum RuleResult {
    Yield(Document),
    Abrupt { inline_throw: bool },
}

pub(super) struct SwitchExpression<'a> {
    pub(super) selector: &'a Document,
    pub(super) rules: Vec<Rule<'a>>,
    pub(super) depth: usize,
}

impl Emitter<'_> {
    /// A default-only JVM switch has no branch convergence at which to split
    /// its rule from its consumer. Prove an expression-only prefix in its
    /// exclusively owned destination, then resume that block at the consuming
    /// constructor instruction with the switch result on the stack.
    pub(super) fn try_default_constructor_switch<'a, 'c>(
        &mut self,
        header: usize,
        region: Region<'_, 'a, 'c>,
        machine: &mut Machine<'a, 'c>,
        depth: usize,
        selector: &Document,
        control: &RangeInclusive<u32>,
    ) -> Option<(usize, usize)> {
        if !machine.supports_switch_expressions() || machine.stack_is_empty() {
            return None;
        }
        let blocks = &self.graph.blocks;
        let dispatch = &self.instructions[blocks[header].instructions.end - 1];
        let Operand::Switch { default, cases } = &dispatch.operand else {
            return None;
        };
        if !cases.is_empty() {
            return None;
        }
        let target = self.graph.block_at(*default)?;
        self.try_default_switch_arm(header, target, region, machine, depth, selector, control, None)
    }

    pub(super) fn try_default_switch_arm<'a, 'c>(
        &mut self,
        header: usize,
        target: usize,
        region: Region<'_, 'a, 'c>,
        machine: &mut Machine<'a, 'c>,
        depth: usize,
        selector: &Document,
        control: &RangeInclusive<u32>,
        constructor_setup: Option<usize>,
    ) -> Option<(usize, usize)> {
        let blocks = &self.graph.blocks;
        let body = &blocks[target];
        if !self.private_switch_block(header, region, target)
            || body.predecessors.as_slice() != [header]
        {
            return None;
        }
        let range = body.instructions.clone();
        let instructions = self.instructions;
        let mut candidates = (range.start + 1..range.end).filter(|&index| instructions[index].opcode == 0xb7).peekable();
        candidates.peek()?;
        let mut arm = machine.switch_arm_entry(control).ok()?;
        let names = machine.local_name_checkpoint();
        let anonymous = machine.switch_anonymous_checkpoint();
        let start = self.lines.len();
        let recovered = (|| {
            let mut cursor = range.start;
            let mut mapped = Vec::new();
            for split in candidates {
                let Tail { effect: Effect::None, offsets, .. } =
                    self.lift_range(target, cursor..split, &mut arm, region, depth + 2, mapped).ok()?
                else {
                    return None;
                };
                if self.lines.len() != start || !arm.same_locals(machine) {
                    return None;
                }
                if constructor_setup.is_some_and(|start| {
                    !machine.proves_constructor_switch(&instructions[start..split], &instructions[split])
                }) {
                    cursor = split;
                    mapped = offsets;
                    continue;
                }
                let Some(mut value) = machine.join_constructor_switch_values(
                    &[&arm], &instructions[split], control, instructions[split - 1].offset,
                ) else {
                    // An inner allocation may finish inside the rule. Keep
                    // lifting it as part of the rule, not as its consumer.
                    cursor = split;
                    mapped = offsets;
                    continue;
                };
                let expression = SwitchExpression {
                    selector,
                    rules: vec![Rule {
                        labels: &[],
                        default: DefaultLabel::Default,
                        statements: Vec::new(),
                        trailing_offsets: offsets,
                        result: RuleResult::Yield(value.yields.pop().expect("one default value")),
                    }],
                    depth,
                };
                machine.push_switch_value(value, expression.render()).ok()?;
                return Some((target, split));
            }
            None
        })();
        if recovered.is_some() {
            machine.commit_switch_dynamic_helpers(&arm);
        } else {
            self.lines.truncate(start);
            machine.restore_local_names(names);
            machine.restore_switch_anonymous_sites(anonymous);
        }
        recovered
    }

    pub(super) fn try_switch_expression<'a, 'c>(
        &mut self,
        header: usize,
        region: Region<'_, 'a, 'c>,
        machine: &mut Machine<'a, 'c>,
        depth: usize,
        selector: &Document,
        groups: &BTreeMap<usize, Vec<CaseLabel>>,
        default: usize,
        join: usize,
        control: &RangeInclusive<u32>,
    ) -> bool {
        if !machine.supports_switch_expressions() {
            return false;
        }
        let Some(proof) = self.switch_region(header, region, groups.keys().copied(), join) else {
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
                        default: (target == default).into(),
                        statements,
                        trailing_offsets: arm.offsets,
                        result,
                    }
                })
                .collect();
            let expression = SwitchExpression {
                selector,
                rules,
                depth,
            };
            machine.push_switch_value(value, expression.render()).ok()
        })();
        if recovered.is_some() {
            machine.commit_switch_dynamic_helpers(&entry);
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

    /// javac can compile a switch used by `if` without ever pushing a
    /// boolean. Recover that predicate only when all rules have the same two
    /// continuations and their private computation leaves no side channels.
    pub(super) fn try_predicate_switch<'a, 'c>(
        &mut self,
        header: usize,
        region: Region<'_, 'a, 'c>,
        machine: &mut Machine<'a, 'c>,
        depth: usize,
        selector: &Document,
        groups: &BTreeMap<usize, Vec<CaseLabel>>,
        default: usize,
        control: &RangeInclusive<u32>,
    ) -> Option<(Condition, RangeInclusive<u32>)> {
        if groups.len() < 2 || !machine.supports_switch_expressions()
            || machine.has_uninitialized_stack() || self.assertion_starts(header)
        {
            return None;
        }
        let blocks = &self.graph.blocks;
        let mut owned = BTreeSet::new();
        let mut exits = None;
        let mut routes = Vec::with_capacity(groups.len());
        let mut last = *control.end();
        for &arm in groups.keys() {
            let body = &blocks[arm];
            if !self.private_switch_block(header, region, arm)
                || body.predecessors.as_slice() != [header]
                || !owned.insert(arm)
            {
                return None;
            }
            let tail = &self.instructions[body.instructions.end - 1];
            let Operand::Branch(taken) = tail.operand else { return None };
            if !matches!(tail.opcode, 0x99..=0xa6 | 0xc6..=0xc7) {
                return None;
            }
            let (taken, fallthrough) = self.branch_targets(arm, taken).ok()?;
            let taken = self.switch_predicate_destination(header, region, arm, taken, &mut owned)?;
            let fallthrough = self.switch_predicate_destination(header, region, arm, fallthrough, &mut owned)?;
            let pair = (taken.min(fallthrough), taken.max(fallthrough));
            if taken == fallthrough || exits.is_some_and(|exits| exits != pair) {
                return None;
            }
            exits = Some(pair);
            routes.push(fallthrough == pair.0);
            last = last.max(tail.offset);
        }
        let (fallthrough, taken) = exits?;
        let last_owned = owned.last().copied()?;
        // In a one-sided `if`, its bypass target is also the common
        // continuation: the other branch legitimately flows into it after
        // executing its body. emit_if stops both arms at that postdominator;
        // only a target that will become an arm entry needs exclusive inputs.
        let join = self.layout.normal_join(header, region).or(region.stop);
        for branch in [taken, fallthrough] {
            let node = &blocks[branch];
            if branch <= last_owned || self.emitted[branch]
                || region.loop_transfer(branch).is_some()
                || !node.exception_predecessors.is_empty()
                || (region.stop != Some(branch)
                    && (!self.layout.inside(branch, region)
                        || !self.exceptions.contains(region.exception_arm, branch)))
                || (join != Some(branch) && node.predecessors.iter().any(|pred| !owned.contains(pred)))
            {
                return None;
            }
        }
        let entry = machine.switch_arm_entry(control).ok()?;
        let names = machine.local_name_checkpoint();
        let anonymous = machine.switch_anonymous_checkpoint();
        let start = self.lines.len();
        let recovered = (|| {
            let mut rules = Vec::with_capacity(groups.len());
            for ((&head, labels), takes_fallthrough) in groups.iter().zip(routes) {
                let mut arm = entry.clone();
                let Tail {
                    effect: Effect::Branch { when_true, when_false, .. },
                    offsets,
                    control: Some(arm_control),
                } = self.lift_block(head, &mut arm, region, depth + 2, Vec::new()).ok()?
                else {
                    return None;
                };
                if self.lines.len() != start || *arm_control.start() <= *control.end()
                    || !arm.same_control_stack(&entry) || !arm.same_locals(&entry)
                {
                    return None;
                }
                rules.push(Rule {
                    labels,
                    default: (head == default).into(),
                    statements: Vec::new(),
                    trailing_offsets: offsets,
                    result: RuleResult::Yield(if takes_fallthrough { when_false } else { when_true }),
                });
            }
            let when_false = SwitchExpression { selector, rules, depth }.render();
            let when_true = surrounded(when_false.clone(), "!(", ")");
            Some((Condition { taken, fallthrough, when_true, when_false }, *control.start()..=last))
        })();
        if recovered.is_some() {
            for block in owned {
                self.emitted[block] = true;
            }
            machine.commit_switch_dynamic_helpers(&entry);
        } else {
            self.lines.truncate(start);
            machine.restore_local_names(names);
            machine.restore_switch_anonymous_sites(anonymous);
        }
        recovered
    }

    fn private_switch_block(&self, header: usize, region: Region<'_, '_, '_>, block: usize) -> bool {
        self.layout.inside(block, region)
            && self.layout.loops[block].is_none()
            && self.plain_switch_block(header, region, block)
    }

    fn plain_switch_block(&self, header: usize, region: Region<'_, '_, '_>, block: usize) -> bool {
        let node = &self.graph.blocks[block];
        let range = node.instructions.clone();
        block > header && !self.emitted[block]
            && region.loop_transfer(block).is_none()
            && !self.assertion_starts(block)
            && self.exceptions.contains(region.exception_arm, block)
            && self.exceptions.at_start(region.exception_arm, block).is_none()
            && node.exception_predecessors.is_empty()
            && node.exception_successors == self.graph.blocks[header].exception_successors
            && !self.exceptions.skips_binding(block)
            && self.exceptions.cleanup_prefix(block) == 0
            && self.exceptions.finally_range(region.exception_arm, block).is_none()
            && self.exceptions.return_split(region.exception_arm, block).is_none()
            && self.exceptions.monitor_acquisition_end(block).is_none()
            && !self.exception_redirects.contains_key(&block)
            && self.exceptions.bypass_cleanup(block) == block
            && region.for_loop_prefix(range.start).is_none()
            && !range.into_iter().any(|index| {
                self.exceptions.skips_instruction(index) || region.for_loop_omits(index)
            })
    }

    /// Follow only an exclusively owned chain of nop/goto bridges. A shared
    /// bridge is already a continuation and must not be consumed per rule.
    fn switch_predicate_destination(
        &self,
        header: usize,
        region: Region<'_, '_, '_>,
        mut from: usize,
        mut destination: usize,
        owned: &mut BTreeSet<usize>,
    ) -> Option<usize> {
        loop {
            let node = &self.graph.blocks[destination];
            let [next] = node.successors.as_slice() else { break };
            let (tail, prefix) = self.instructions[node.instructions.clone()].split_last()?;
            if node.predecessors.as_slice() != [from]
                || !matches!(tail.opcode, 0x00 | 0xa7 | 0xc8)
                || prefix.iter().any(|op| op.opcode != 0)
                || !self.private_switch_block(header, region, destination)
            {
                break;
            }
            if *next <= destination || !owned.insert(destination) {
                return None;
            }
            from = destination;
            destination = *next;
        }
        Some(destination)
    }

    pub(super) fn switch_region(
        &self,
        header: usize,
        region: Region<'_, '_, '_>,
        targets: impl Iterator<Item = usize> + Clone,
        join: usize,
    ) -> Option<SwitchRegion> {
        self.switch_region_entries(header, region, targets, join, |_, pred| pred == header)
    }

    pub(super) fn switch_region_entries(
        &self,
        header: usize,
        region: Region<'_, '_, '_>,
        targets: impl Iterator<Item = usize> + Clone,
        join: usize,
        accepts_entry: impl Fn(usize, usize) -> bool,
    ) -> Option<SwitchRegion> {
        if join <= header
            || self.emitted[join]
            || targets.clone().any(|target| target == join)
            || region.loop_transfer(join).is_some()
        {
            return None;
        }
        let switch_region = region.switch_body(Some(join));
        let blocks = &self.graph.blocks;
        if !blocks[join].exception_predecessors.is_empty()
            || blocks[join].exception_successors != blocks[header].exception_successors
            || targets.clone().any(|target| !self.layout.inside(target, switch_region))
        {
            return None;
        }
        let mut owners = BTreeMap::new();
        let mut pending = Vec::new();
        let mut reaches_join = false;
        let mut last = self.offset(header);
        for target in targets {
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
                    owners.get(pred) != Some(&owner)
                        && (block != owner || !accepts_entry(block, *pred))
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
    pub(super) fn render(self) -> Document {
        let mut document = Document::from("switch (");
        document.append_ref(self.selector);
        document.push_str(") {");
        for Rule {
            labels,
            default,
            statements,
            trailing_offsets,
            result,
        } in self.rules
        {
            document.hard_line(1);
            document.anchor_offsets(
                labels
                    .iter()
                    .flat_map(|label| label.offsets.iter().copied()),
            );
            match default {
                // Ordinary integer keys sharing the default target are
                // covered by default; null is distinct in a pattern switch.
                DefaultLabel::Default => document.push_str("default"),
                DefaultLabel::NullDefault => document.push_str("case null, default"),
                DefaultLabel::Absent => {
                    document.push_str("case ");
                    for (index, label) in labels.iter().enumerate() {
                        if index != 0 {
                            document.push_str(", ");
                        }
                        document.append_ref(&label.text);
                    }
                }
            }
            document.push_str(" -> ");
            match result {
                RuleResult::Yield(mut value) if statements.is_empty() => {
                    document.anchor_offsets(trailing_offsets);
                    value.offset_relative_depth(1);
                    document.append(value);
                    document.push(';');
                }
                RuleResult::Abrupt { inline_throw: true } => {
                    document.anchor_offsets(trailing_offsets);
                    let [line] = <[_; 1]>::try_from(statements).expect("one inline throw");
                    Self::append_statement(&mut document, line, 1);
                }
                result => {
                    document.push('{');
                    for line in statements.into_iter().filter(|line| !line.detached_declaration) {
                        let depth = line.depth - self.depth;
                        document.hard_line(depth);
                        Self::append_statement(&mut document, line, depth);
                    }
                    if let RuleResult::Yield(mut value) = result {
                        document.hard_line(2);
                        document.anchor_offsets(trailing_offsets);
                        document.push_str("yield ");
                        value.offset_relative_depth(2);
                        document.append(value);
                        document.push(';');
                    } else {
                        document.anchor_offsets(trailing_offsets);
                    }
                    document.hard_line(1);
                    document.push('}');
                }
            }
        }
        document.hard_line(0);
        document.push('}');
        document
    }

    fn append_statement(document: &mut Document, mut line: Line, depth: usize) {
        document.anchor_offsets(line.offsets);
        line.text.offset_relative_depth(depth);
        document.append(line.text);
    }
}

#[cfg(test)]
#[path = "switch_expression_tests.rs"]
mod tests;
