use std::{collections::BTreeSet, mem, ops::RangeInclusive};

use crate::{bytecode::{Instruction, Operand}, cfg::{ControlFlowGraph, NaturalLoop}, lift::Machine, source_text::Document};

use super::{Emitter, Region, StructureError};
use crate::structure::protected::Exceptions;

pub(in crate::structure) struct ConditionalCase {
    pub(in crate::structure) head: usize,
    arm: usize,
    header: usize,
    pub(in crate::structure) continuation: usize,
    join: usize,
    shared_tail: Option<usize>,
    labeled_fallthrough: bool,
    guards: BTreeSet<usize>,
}

impl ConditionalCase {
    pub(in crate::structure) fn prove(
        graph: &ControlFlowGraph,
        instructions: &[Instruction],
        exceptions: &Exceptions,
        cycle: &NaturalLoop,
        normal: usize,
        exits: &BTreeSet<usize>,
        postdominator: impl FnOnce(usize) -> Option<usize>,
    ) -> Option<Self> {
        let cfg = &graph.blocks;
        let header = cycle.header;
        let cyclic = |block| cycle.blocks.binary_search(&block).is_ok();
        let last = |block: usize| &instructions[cfg[block].instructions.end - 1];
        // Walk out through the case's single-entry prefix, not across another
        // case or a conditional. Only a real switch may own its continuation.
        let mut arm = header;
        let head = loop {
            let mut incoming = cfg[arm].predecessors.iter().copied().filter(|&pred| !cyclic(pred));
            let pred = incoming.next()?;
            if incoming.next().is_some() || pred >= arm { return None; }
            if matches!(last(pred).opcode, 0xaa | 0xab) { break pred; }
            if pred + 1 != arm || cfg[pred].successors != [arm] { return None; }
            arm = pred;
        };
        let Operand::Switch { default, cases } = &last(head).operand else { return None; };
        let join = graph.block_at(*default)?;
        if postdominator(head) != Some(join) || normal <= header || normal >= join { return None; }
        let mut targets = cfg[head].successors.iter().copied().filter(|&target| target != join);
        let continuation = targets.clone().filter(|&target| target > arm).min()?;
        if normal >= continuation || continuation >= join
            || targets.any(|target| target < arm || target >= join)
            || cycle.blocks.iter().any(|&block| block < header || block >= continuation)
        {
            return None;
        }
        if (head..=join).any(|block| {
            let node = &cfg[block];
            !node.exception_predecessors.is_empty() || !node.exception_successors.is_empty()
                || !exceptions.contains(None, block) || exceptions.at_start(None, block).is_some()
                || exceptions.bypass_cleanup(block) != block
                || (block != head && node.predecessors.iter().any(|&pred| pred < head || pred >= join))
                || node.instructions.clone().any(|index| {
                    exceptions.skips_instruction(index) || matches!(instructions[index].opcode, 0xc2 | 0xc3)
                })
        }) {
            return None;
        }
        let arm_key = cases.iter().find_map(|&(key, target)| (graph.block_at(target) == Some(arm)).then_some(key))?;
        let continuation_key = cases.iter().find_map(|&(key, target)| {
            (graph.block_at(target) == Some(continuation)).then_some(key)
        })?;
        if cases.iter().any(|&(key, target)| {
            graph.block_at(target).is_none_or(|target| target == join || (target != arm && key < arm_key))
        }) {
            return None;
        }

        // The tested departure has its own linear tail. No other case may
        // enter it; its only exit skips the following case(s).
        let mut owned = BTreeSet::new();
        let mut block = normal;
        let mut normal_last = None;
        loop {
            if !(header..continuation).contains(&block) || cyclic(block) || !owned.insert(block)
                || normal_last.is_some_and(|pred| cfg[block].predecessors != [pred])
            {
                return None;
            }
            let &[next] = cfg[block].successors.as_slice() else { return None; };
            if next == join {
                if !matches!(last(block).opcode, 0xa7 | 0xc8) { return None; }
                break;
            }
            if next <= block { return None; }
            normal_last = Some(block);
            block = next;
        }

        // Other departures must be disjoint linear exits from the cyclic
        // core, heading to the tested tail or to the next dispatch entry.
        let mut normal_sources = 0;
        let mut continuation_source = None;
        for &first in exits {
            let mut block = first;
            let mut pred = None;
            loop {
                let sole_source = |source| cfg[block].predecessors.as_slice() == [source];
                if block == normal {
                    normal_sources += pred.map_or_else(|| {
                        cfg[normal].predecessors.iter().filter(|&&pred| cyclic(pred)).count()
                    }, |_| 1);
                    break;
                }
                if block == continuation {
                    let source = pred.or_else(|| {
                        let mut predecessors = cfg[block].predecessors.iter().copied().filter(|&pred| cyclic(pred));
                        let first = predecessors.next()?;
                        predecessors.next().is_none().then_some(first)
                    })?;
                    if continuation_source.replace(source).is_some() { return None; }
                    break;
                }
                if !(header..continuation).contains(&block) || cyclic(block) || !owned.insert(block)
                    || !pred.map_or_else(|| {
                        matches!(cfg[block].predecessors.as_slice(), [source] if cyclic(*source))
                    }, sole_source)
                {
                    return None;
                }
                let &[next] = cfg[block].successors.as_slice() else { return None; };
                if next <= block { return None; }
                pred = Some(block);
                block = next;
            }
        }
        let continuation_source = continuation_source?;
        if normal_sources == 0 || cfg[normal].predecessors.len() != normal_sources {
            return None;
        }
        owned.extend(arm..header);
        owned.extend(cycle.blocks.iter().copied());

        // Dispatch to the following case and fallthrough share the same
        // physical body. Prove all other case bodies are independent, so a
        // promoted tail can be emitted once outside the switch.
        for &target in &cfg[head].successors {
            if target == join || target == arm { continue; }
            let incoming = &cfg[target].predecessors;
            if !incoming.contains(&head) || if target == continuation {
                incoming.len() != 2 || !incoming.contains(&continuation_source)
            } else { incoming.len() != 1 } {
                return None;
            }
            let mut block = target;
            while block != join {
                if !(continuation..join).contains(&block) || !owned.insert(block) { return None; }
                let &[next] = cfg[block].successors.as_slice() else { return None; };
                if next <= block || (next != join && cfg[next].predecessors != [block]) { return None; }
                block = next;
            }
        }
        if owned.len() != join - arm { return None; }

        let shared_tail = (normal_sources > 1).then_some(normal);
        let labeled_fallthrough = shared_tail.is_some() && cases.iter().any(|&(key, target)| {
            arm_key < key && key < continuation_key && graph.block_at(target) != Some(arm)
        });
        Some(Self { head, arm, header, continuation, join, shared_tail, labeled_fallthrough, guards: exits.clone() })
    }

    pub(in crate::structure) fn loop_boundary(&self, block: usize) -> bool {
        block == self.join || Some(block) == self.shared_tail
    }

    pub(in crate::structure) fn switch_join(&self) -> usize {
        if self.shared_tail.is_some() { self.continuation } else { self.join }
    }

    pub(in crate::structure) fn falls_through(&self, target: usize, next: usize) -> bool {
        target == self.arm && next == self.continuation && !self.labeled_fallthrough
    }

    pub(in crate::structure) fn omit_default(&self) -> bool {
        self.shared_tail.is_none()
    }
}

pub(in crate::structure) struct ConditionalCaseScope<'r, 'a, 'c> {
    plan: &'r ConditionalCase,
    baseline: &'r Machine<'a, 'c>,
    outer_label: String,
    tail_label: Option<String>,
    switch_label: Option<String>,
}

impl ConditionalCaseScope<'_, '_, '_> {
    pub(in crate::structure) fn plan(&self) -> &ConditionalCase {
        self.plan
    }

    pub(in crate::structure) fn guard(&self, arm: usize, region: Region<'_, '_, '_>) -> bool {
        region.loop_header == Some(self.plan.header) && self.plan.guards.contains(&arm)
    }

    fn label(&self, block: usize, region: Region<'_, '_, '_>) -> Option<&str> {
        let inside_loop = region.loop_header == Some(self.plan.header);
        if region.exception_arm.is_some() { return None; }
        if block == self.plan.join && (inside_loop || self.plan.shared_tail.is_some()) {
            Some(&self.outer_label)
        } else if inside_loop && self.plan.shared_tail == Some(block) {
            self.tail_label.as_deref()
        } else if inside_loop && block == self.plan.continuation {
            self.switch_label.as_deref()
        } else {
            None
        }
    }
}

impl Emitter<'_> {
    pub(super) fn emit_conditional_case_switch<'a, 'c>(
        &mut self,
        plan: &ConditionalCase,
        region: Region<'_, 'a, 'c>,
        machine: &mut Machine<'a, 'c>,
        depth: usize,
        selector: Document,
        offsets: &mut Vec<u32>,
        control: RangeInclusive<u32>,
    ) -> Result<Option<usize>, StructureError> {
        if region.loop_header.is_some() || region.exception_arm.is_some() || region.label_scope().is_some()
            || region.predicate.is_some() || region.conditional_case_scope().is_some()
            || !self.layout.inside(plan.join, region)
            || (plan.head + 1..=plan.join).any(|block| self.emitted[block] || !self.layout.inside(block, region)
                && !self.layout.direct_loop_member(block, plan.header))
        {
            return Err(self.unstructured(plan.head));
        }
        let scope = ConditionalCaseScope {
            plan,
            baseline: machine,
            outer_label: format!("label{}", self.offset(plan.join)),
            tail_label: plan.shared_tail.map(|tail| format!("label{}", self.offset(tail))),
            switch_label: plan.labeled_fallthrough.then(|| format!("label{}", self.offset(plan.continuation))),
        };
        let switch_depth = if let Some(tail) = &scope.tail_label {
            self.push(depth, format!("{}: {{", scope.outer_label), Vec::new());
            self.push(depth + 1, format!("{tail}: {{"), Vec::new());
            if let Some(label) = &scope.switch_label {
                self.push(depth + 2, format!("{label}:"), Vec::new());
            }
            depth + 2
        } else {
            self.push(depth, format!("{}:", scope.outer_label), Vec::new());
            depth
        };
        let case_region = region.conditional_case_body(&scope);
        let mut body = machine.clone();
        let next = self.emit_switch(plan.head, case_region, &mut body, switch_depth, selector, offsets, control, None)?;
        if next != Some(plan.switch_join()) {
            return Err(self.unstructured(plan.head));
        }
        if let Some(tail) = plan.shared_tail {
            // This is the real following case's body, reached both by switch
            // dispatch and from the loop. The switch emitted only its label.
            let first = self.lines.len();
            if self.region(plan.continuation, case_region, &mut body, switch_depth)? {
                return Err(self.unstructured(plan.continuation));
            }
            if let Some(line) = self.lines.get_mut(first) { line.sequence_boundary = true; }
            self.syntax(depth + 1, "}");
            let normal = self.branch_arm(tail, region.branch(Some(plan.join)), machine, depth + 1)?;
            let end = normal.exit.ok_or_else(|| self.unstructured(tail))?;
            self.check_conditional_case_exit(plan.join, &end, machine)?;
            self.syntax(depth, "}");
        } else {
            self.check_conditional_case_exit(plan.join, &body, machine)?;
        }
        Ok(Some(plan.join))
    }

    fn check_conditional_case_exit<'a, 'c>(
        &mut self,
        block: usize,
        machine: &Machine<'a, 'c>,
        baseline: &Machine<'a, 'c>,
    ) -> Result<(), StructureError> {
        self.require_empty_stack(machine, block)?;
        if !machine.same_live_loop_bindings(baseline, |slot| self.local_is_live(block, slot)) {
            return Err(StructureError::LocalJoin { offset: self.offset(block) });
        }
        Ok(())
    }

    pub(in crate::structure) fn record_conditional_case_exit<'a, 'c>(
        &mut self,
        block: usize,
        region: Region<'_, 'a, 'c>,
        machine: &Machine<'a, 'c>,
        depth: usize,
        offsets: &mut Vec<u32>,
    ) -> Result<bool, StructureError> {
        let Some(scope) = region.conditional_case_scope() else { return Ok(false); };
        let Some(label) = scope.label(block, region) else { return Ok(false); };
        self.check_conditional_case_exit(block, machine, scope.baseline)?;
        self.push(depth, format!("break {label};"), mem::take(offsets));
        Ok(true)
    }

    pub(in crate::structure) fn map_conditional_case_jump(
        &self,
        block: usize,
        target: usize,
        region: Region<'_, '_, '_>,
        offsets: &mut Vec<u32>,
    ) {
        if let Some(scope) = region.conditional_case_scope()
            && target != scope.plan.shared_tail.unwrap_or(usize::MAX)
            && scope.label(target, region).is_some()
        {
            offsets.push(self.instructions[self.graph.blocks[block].instructions.end - 1].offset);
        }
    }
}
