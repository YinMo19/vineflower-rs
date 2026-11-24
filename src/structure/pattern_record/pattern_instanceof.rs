// Based on Vineflower's IfPatternMatchProcessor (Apache-2.0).

use std::ops::Range;

use crate::structure::{Condition, Emitter, StructureError, instanceof_patterns::Binding};

use super::{
    BTreeMap, BTreeSet, ControlFlowGraph, Document, Instruction, Machine, Operand, Pattern,
    Prefix, Site, cast_type, local, owns_prefix, temps_are_dead,
};

pub(super) struct Instance {
    pattern: Pattern,
    selector: u16,
    cast_receiver: bool,
    success: u32,
    failure: u32,
    offsets: Range<u32>,
}

pub(super) struct Projection {
    pub(super) branch: u32,
    pub(super) instance: Instance,
    pub(super) removed: Range<usize>,
    pub(super) accesses: BTreeSet<usize>,
    pub(super) slots: Slots,
}

pub(super) struct Slots {
    success: u32,
    failure: u32,
    hidden: BTreeSet<u16>,
    writes_on_failure: BTreeSet<u16>,
}

impl Instance {
    pub(super) fn prove(
        instructions: &[Instruction],
        graph: &ControlFlowGraph,
        accesses: &BTreeMap<usize, usize>,
        machine: &Machine<'_, '_>,
        head: usize,
    ) -> Option<Projection> {
        let node = &graph.blocks[head];
        // A naked local load cannot absorb an earlier assignment expression
        // when the generic instanceof document is replaced.
        let [load, test, branch] = &instructions[node.instructions.clone()] else { return None };
        if branch.opcode != 0x99 || !node.exception_predecessors.is_empty()
            || !node.exception_successors.is_empty()
            || node.predecessors.iter().any(|&pred| {
                // The projected test is emitted by the normal if owner, not a
                // loop header or a conditional predecessor's speculative fold.
                pred >= head || graph.blocks[pred].successors != [head]
            })
        {
            return None;
        }
        let Operand::Branch(failure) = branch.operand else { return None };
        let failed = graph.block_at(failure)?;
        let selector = local(load, false, true)?;
        let ty = cast_type(machine, test, 0xc1)?;
        let start = node.instructions.end;
        let entered = graph.block_at(instructions.get(start)?.offset)?;
        if node.successors != [failed, entered] || failed == entered
            || graph.blocks[entered].predecessors != [head]
        {
            return None;
        }
        let mut cursor = start;
        if local(&instructions[cursor], false, true)? != selector { return None; }
        cursor += 1;
        let cast_receiver = instructions.get(cursor)?.opcode == 0xc0;
        if cast_receiver {
            if cast_type(machine, &instructions[cursor], 0xc0)? != ty { return None; }
            cursor += 1;
        }
        let alias = local(instructions.get(cursor)?, true, true)?;
        let mut parser = Prefix {
            instructions, graph, pool: machine.constant_pool(), accesses, machine,
            pos: cursor + 1, alias: selector, restart: None, dispatch: head, key: 0,
            first_temporary: machine.pattern_raw_parameter_slots(), failure: Some(failure),
            wrapper: None,
            temporaries: BTreeSet::new(), receivers: BTreeSet::new(), leaves: BTreeSet::new(),
            used_accesses: BTreeSet::new(), retries: BTreeSet::new(), may_fail: false,
        };
        let pattern = parser.record(&ty, alias, 0)?;
        let resume = parser.pos;
        let success = instructions.get(resume)?.offset;
        let removed = start..resume;
        if success == failure || parser.used_accesses.is_empty()
            || (instructions[start].offset..success).contains(&failure)
            || !owns_prefix(instructions, graph, head, start, resume,
                |index| removed.contains(&index), &parser.retries, Some(failure))
        {
            return None;
        }
        let mut writes_on_failure = parser.leaves;
        if parser.may_fail {
            // A later component may fail after earlier bindings and scratch
            // locals have been written. Neither may escape the false edge.
            writes_on_failure.extend(parser.temporaries.iter().copied());
        }
        Some(Projection {
            branch: branch.offset,
            instance: Self {
                pattern, selector, cast_receiver, success, failure,
                offsets: instructions[start].offset..success,
            },
            removed,
            accesses: parser.used_accesses,
            slots: Slots { success, failure, hidden: parser.temporaries, writes_on_failure },
        })
    }

    pub(super) fn definition(&self) -> (u32, &Pattern) {
        (self.success, &self.pattern)
    }
}

impl Slots {
    pub(super) fn verify(
        self,
        instructions: &[Instruction],
        graph: &ControlFlowGraph,
        bindings: &BTreeMap<u32, &Pattern>,
    ) -> Option<()> {
        let success = graph.block_at(self.success)?;
        let failure = graph.block_at(self.failure)?;
        (temps_are_dead(instructions, graph, bindings, &[success], &self.hidden)
            && temps_are_dead(instructions, graph, bindings, &[failure], &self.writes_on_failure))
            .then_some(())
    }
}

impl Emitter<'_> {
    pub(in crate::structure) fn has_record_instance(&self, block: usize) -> bool {
        self.record_patterns.is_some_and(|plans| {
            let branch = &self.instructions[self.graph.blocks[block].instructions.end - 1];
            plans.instances.contains_key(&branch.offset)
        })
    }

    pub(in crate::structure) fn record_instanceof_binding(
        &self,
        block: usize,
        machine: &mut Machine<'_, '_>,
        condition: &mut Condition,
        offsets: &mut Vec<u32>,
    ) -> Result<Option<Binding>, StructureError> {
        let Some(plans) = self.record_patterns else { return Ok(None) };
        let branch = &self.instructions[self.graph.blocks[block].instructions.end - 1];
        let Some(instance) = plans.instances.get(&branch.offset) else { return Ok(None) };
        let success = condition.fallthrough;
        if self.offset(success) != instance.success || self.offset(condition.taken) != instance.failure {
            return Err(self.unstructured(block));
        }
        let Pattern::Record(ty, _) = &instance.pattern else { return Err(self.unstructured(block)) };
        let mut positive = machine.record_if_selector(instance.selector, ty, instance.cast_receiver)?;
        let mut locals = Vec::new();
        let pattern = instance.pattern.render_with(machine, &mut |machine, ty, store, cast, slot| {
            let (document, local) = machine.prepare_record_if_component(ty, cast, store, slot)?;
            locals.push(local);
            Ok(document)
        })?;
        positive.push_str(" instanceof ");
        positive.append(pattern);
        let mut inverse = Document::from("!(");
        inverse.append(positive.clone());
        inverse.push(')');
        condition.when_false = positive;
        condition.when_true = inverse;
        offsets.extend(instance.offsets.clone());
        plans.claimed.borrow_mut().insert(Site::Instance(branch.offset));
        Ok(Some(Binding::record(success, locals)))
    }
}
