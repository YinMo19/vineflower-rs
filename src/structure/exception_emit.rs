// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use std::{mem, ops::Range};

use crate::bytecode::{Instruction, Operand};
use crate::lift::{Effect, Machine};

use super::protected::{
    Catch, ExceptionId, Monitor, ProtectedRegion, local_touches, reference_load, reference_store,
};
use super::{Emitter, Region, StructureError};

struct Resource {
    acquisition: usize,
    slot: u16,
    normal_cleanup: usize,
    continuation: usize,
    skipped: Vec<usize>,
}

impl Emitter<'_> {
    pub(super) fn emit_exception<'a, 'c>(
        &mut self,
        id: ExceptionId,
        region: Region<'_, 'a, 'c>,
        machine: &mut Machine<'a, 'c>,
        depth: usize,
        pending: &mut Vec<u32>,
    ) -> Result<Option<usize>, StructureError> {
        let exceptions = self.exceptions;
        let shape = exceptions.region(id);
        if !machine.this_is_initialized() {
            return Err(self.unstructured(shape.start));
        }
        if let Some(monitor) = &shape.monitor {
            return self.emit_monitor(shape, monitor, region, machine, depth, pending);
        }
        self.require_empty_stack(machine, shape.start)?;
        pending.clear();
        if let Some(resource) = self.prove_resource(shape, region, machine, depth)? {
            return self.emit_resource(shape, resource, region, machine, depth).map(Some);
        }
        let (clauses, scope) = if let Some(inner) = exceptions.catches_of_finally(shape) {
            (inner, region.exception(shape.join, shape.body, Some(machine)))
        } else {
            (shape, region)
        };
        self.syntax(depth, "try {");
        let mut reaches_join = self.scoped_arm(
            clauses.start,
            scope.exception(clauses.join, clauses.body, Some(machine)),
            machine,
            depth + 1,
        )?;
        for catch in &clauses.catches {
            let store = &self.instructions[self.graph.blocks[catch.start].instructions.start];
            let mut body = machine.clone();
            let (types, name) = match catch.alternatives.as_slice() {
                &[single] => body.bind_caught_exception(single, store)?,
                types => {
                    // The verifier supplies the handler's actual local type;
                    // using an arbitrary alternative can incorrectly narrow
                    // later expressions referring to the catch parameter.
                    let common = body.caught_exception_stack_type(store.offset)?
                        .ok_or(StructureError::ExceptionHandlers)?;
                    let (_, name) = body.bind_caught_exception(common, store)?;
                    let mut union = String::new();
                    for &alternative in types {
                        if !union.is_empty() {
                            union.push_str(" | ");
                        }
                        union.push_str(&body.render_catch_type(alternative)?);
                    }
                    (union, name)
                }
            };
            self.push(
                depth,
                format!("}} catch ({types} {name}) {{"),
                (store.offset..store.offset + store.len).collect(),
            );
            if self.region(
                catch.start,
                scope.exception(clauses.join, catch.arm, None),
                &mut body,
                depth + 1,
            )? {
                let join = shape.join.ok_or(StructureError::ExceptionHandlers)?;
                Self::check_scope(body, machine, self.offset(join))?;
                reaches_join = true;
            }
        }
        let mut continuation = shape.join;
        if let Some(finally) = &shape.finally {
            self.syntax(depth, "} finally {");
            let mut body = machine.clone();
            let mut offsets = Vec::new();
            if let Some(branch) = finally.branched() {
                if finally.start() != branch.entry
                    && mem::replace(&mut self.emitted[finally.start()], true)
                {
                    return Err(self.unstructured(finally.start()));
                }
                if !self.region_with_offsets(
                    branch.entry,
                    region.exception(Some(finally.block()), finally.arm, None),
                    &mut body,
                    depth + 1,
                    &mut offsets,
                )? {
                    return Err(self.unstructured(branch.entry));
                }
                for &copy in &branch.removed {
                    if !self.exceptions.contains(region.exception_arm, copy)
                        || mem::replace(&mut self.emitted[copy], true)
                    {
                        return Err(self.unstructured(copy));
                    }
                }
                continuation = branch.continuation;
            } else if finally.start() != finally.block()
                && mem::replace(&mut self.emitted[finally.start()], true)
            {
                return Err(self.unstructured(finally.start()));
            }
            if mem::replace(&mut self.emitted[finally.block()], true) {
                return Err(self.unstructured(finally.block()));
            }
            let cleanup = self.lift_block(
                finally.block(),
                &mut body,
                region.exception(None, finally.arm, None),
                depth + 1,
                offsets,
            )?;
            if !matches!(cleanup.effect, Effect::None) {
                return Err(self.unstructured(finally.block()));
            }
            Self::check_scope(body, machine, self.offset(finally.block()))?;
        }
        self.syntax(depth, "}");
        Ok(if reaches_join { continuation } else { None })
    }

    fn emit_monitor<'a, 'c>(
        &mut self,
        shape: &ProtectedRegion,
        monitor: &Monitor,
        region: Region<'_, 'a, 'c>,
        machine: &mut Machine<'a, 'c>,
        depth: usize,
        pending: &mut Vec<u32>,
    ) -> Result<Option<usize>, StructureError> {
        let enter = &self.instructions[monitor.plan.enter_index()];
        let lock = machine.take_monitor_lock(enter)?;
        let mut offsets = mem::take(pending);
        for statement in machine.take_prelude() {
            self.push(depth, statement, mem::take(&mut offsets));
        }
        offsets.extend(enter.offset..enter.offset + enter.len);
        self.push(depth, format!("synchronized ({lock}) {{"), offsets);
        for block in monitor.plan.handler_blocks() {
            if mem::replace(&mut self.emitted[block], true) {
                return Err(self.unstructured(block));
            }
        }
        let body_start = self.lines.len();
        let reaches = self.scoped_arm(
            shape.start,
            region.exception(shape.join, shape.body, Some(machine)),
            machine,
            depth + 1,
        )?;
        if self.lines.len() == body_start {
            self.syntax(depth + 1, ";");
            self.syntax(depth, "}");
        } else if let Some(index) = monitor.plan.release_index(shape.start)
            && self.graph.blocks[shape.start].instructions.end == index + 1
        {
            self.push(depth, "}".into(), vec![self.instructions[index].offset]);
        } else {
            self.syntax(depth, "}");
        }
        Ok(if reaches { shape.join } else { None })
    }

    fn emit_resource<'a, 'c>(
        &mut self,
        shape: &ProtectedRegion,
        resource: Resource,
        region: Region<'_, 'a, 'c>,
        machine: &mut Machine<'a, 'c>,
        depth: usize,
    ) -> Result<usize, StructureError> {
        let line = &mut self.lines[resource.acquisition];
        line.text.pop(); // Verified declaration terminator.
        line.text = format!("try ({}) {{", line.text);
        for block in resource.skipped {
            self.emitted[block] = true;
        }
        if !self.scoped_arm(
            shape.start,
            region.exception(Some(resource.normal_cleanup), shape.body, Some(machine)),
            machine,
            depth + 1,
        )? {
            return Err(self.unstructured(shape.start));
        }
        self.syntax(depth, "}");
        machine.forget_resource_local(resource.slot);
        Ok(resource.continuation)
    }

    // javac's modern resource lowering has two close paths. The exception
    // path closes under a Throwable handler which suppresses on the original
    // exception, then rethrows that exact object. Verify the local identities,
    // exception coverage, and every edge in those paths before hiding them.
    fn prove_resource(
        &mut self,
        shape: &ProtectedRegion,
        region: Region<'_, '_, '_>,
        machine: &Machine<'_, '_>,
        depth: usize,
    ) -> Result<Option<Resource>, StructureError> {
        let Some(primary) = throwable_catch(shape, machine)? else {
            return Ok(None);
        };
        let Some(normal_cleanup) = shape.join else {
            return Ok(None);
        };
        let &[predecessor] = self.graph.blocks[shape.start].predecessors.as_slice() else {
            return Ok(None);
        };
        let Some(initialization) = self.block_instructions(predecessor).last() else {
            return Ok(None);
        };
        let Some(slot) = reference_store(initialization) else {
            return Ok(None);
        };
        let Some((ty, name)) = machine.resource_local(slot) else {
            return Ok(None);
        };
        let Some(acquisition) = self.lines.len().checked_sub(1) else {
            return Ok(None);
        };
        let line = &self.lines[acquisition];
        if self.graph.blocks[predecessor].successors != [shape.start]
            || !self.exceptions.contains(region.exception_arm, predecessor)
            || line.depth != depth
            || !line.offsets.contains(&initialization.offset)
            || !line.text.ends_with(';')
            || line.text.strip_prefix(&ty)
                .and_then(|text| text.strip_prefix(' '))
                .and_then(|text| text.strip_prefix(name))
                .is_none_or(|text| !text.starts_with(" = "))
        {
            return Ok(None);
        }

        let primary_code = self.block_instructions(primary.start);
        let Some(original) = primary_code.first().and_then(reference_store) else {
            return Ok(None);
        };
        if original == slot {
            return Ok(None);
        }
        let (exceptional_close, null_rethrow) = match primary_code {
            [_] => {
                let &[close] = self.graph.blocks[primary.start].successors.as_slice() else {
                    return Ok(None);
                };
                (close, None)
            }
            [_, load, test] if reference_load(load) == Some(slot) && test.opcode == 0xc6 => {
                let &[rethrow, close] = self.graph.blocks[primary.start].successors.as_slice()
                else {
                    return Ok(None);
                };
                (close, Some(rethrow))
            }
            _ => return Ok(None),
        };
        let Some(inner) = self.exceptions.at_start(Some(primary.arm), exceptional_close) else {
            return Ok(None);
        };
        let inner = self.exceptions.region(inner);
        let Some(suppression) = throwable_catch(inner, machine)? else {
            return Ok(None);
        };
        let Some(rethrow) = inner.join else {
            return Ok(None);
        };
        let [load, throw] = self.block_instructions(rethrow) else {
            return Ok(None);
        };
        if null_rethrow.is_some_and(|target| target != rethrow)
            || reference_load(load) != Some(original)
            || throw.opcode != 0xbf
        {
            return Ok(None);
        }
        let Some(close_method) = self.close_method(exceptional_close, slot, machine)? else {
            return Ok(None);
        };
        let Some(mut after) = self.after_prefix(exceptional_close, 2) else {
            return Ok(None);
        };
        let mut skipped = vec![primary.start, exceptional_close, suppression.start, rethrow];
        // The end of the inner exception interval often forces a separate
        // goto block between close() and the rethrow.
        while after != rethrow {
            if skipped.contains(&after)
                || !self.exceptions.contains(Some(inner.body), after)
                || self.block_instructions(after).len() != 1
            {
                return Ok(None);
            }
            let Some(next) = self.after_prefix(after, 0) else {
                return Ok(None);
            };
            skipped.push(after);
            after = next;
        }

        let [store, primary_arg, suppressed_arg, add_suppressed, ..] =
            self.block_instructions(suppression.start)
        else {
            return Ok(None);
        };
        let Some(suppressed) = reference_store(store) else {
            return Ok(None);
        };
        let Some(add_suppressed_index) = invocation_index(add_suppressed) else {
            return Ok(None);
        };
        if suppressed == original
            || suppressed == slot
            || reference_load(primary_arg) != Some(original)
            || reference_load(suppressed_arg) != Some(suppressed)
            || add_suppressed.opcode != 0xb6
            || machine.exception_member(add_suppressed_index)?
                != ("java/lang/Throwable", "addSuppressed", "(Ljava/lang/Throwable;)V")
            || self.after_prefix(suppression.start, 4) != Some(rethrow)
            || !self.exceptions.arm_blocks(primary.arm).all(|block| skipped.contains(&block))
        {
            return Ok(None);
        }

        let (normal_close, null_continuation) = if null_rethrow.is_some() {
            let [load, test] = self.block_instructions(normal_cleanup) else {
                return Ok(None);
            };
            let &[continuation, close] = self.graph.blocks[normal_cleanup].successors.as_slice()
            else {
                return Ok(None);
            };
            if reference_load(load) != Some(slot) || test.opcode != 0xc6 {
                return Ok(None);
            }
            skipped.push(normal_cleanup);
            (close, Some(continuation))
        } else {
            if !self.allocates_nonnull(predecessor, machine)? {
                return Ok(None);
            }
            (normal_cleanup, None)
        };
        let Some(continuation) = self.after_prefix(normal_close, 2) else {
            return Ok(None);
        };
        if null_continuation.is_some_and(|target| target != continuation)
            || self.close_method(normal_close, slot, machine)? != Some(close_method)
        {
            return Ok(None);
        }
        skipped.push(normal_close);

        let ambient = &self.graph.blocks[normal_close].exception_successors;
        if self.graph.blocks[suppression.start].exception_successors != *ambient
            || self.graph.blocks[rethrow].exception_successors != *ambient
            || !self.graph.blocks[exceptional_close].exception_successors.iter().copied()
                .filter(|&handler| handler != suppression.start).eq(ambient.iter().copied())
            || skipped.contains(&continuation)
            || self.exceptions.at_start(region.exception_arm, normal_cleanup).is_some()
            || self.exceptions.at_start(region.exception_arm, normal_close).is_some()
            || skipped.iter().any(|&block| {
                self.emitted[block]
                    || self.exceptions.cleanup_prefix(block) != 0
                    || !self.exceptions.contains(region.exception_arm, block)
                    || self.graph.blocks[block].predecessors.iter().any(|pred| {
                        !skipped.contains(pred) && !self.exceptions.contains(Some(shape.body), *pred)
                    })
            })
            || self.exceptions.arm_blocks(shape.body).any(|block| {
                self.block_instructions(block).iter().any(|instruction| {
                    matches!(instruction.opcode, 0xac..=0xb1)
                        || is_slot_write(instruction, slot)
                })
            })
            || self.layout.local_is_live(self.graph, self.instructions, continuation, slot)
        {
            return Ok(None);
        }
        Ok(Some(Resource { acquisition, slot, normal_cleanup, continuation, skipped }))
    }

    fn close_method(
        &self,
        block: usize,
        slot: u16,
        machine: &Machine<'_, '_>,
    ) -> Result<Option<u16>, StructureError> {
        let [load, invoke, ..] = self.block_instructions(block) else {
            return Ok(None);
        };
        if reference_load(load) != Some(slot) || !matches!(invoke.opcode, 0xb6 | 0xb9) {
            return Ok(None);
        }
        let Some(index) = invocation_index(invoke) else {
            return Ok(None);
        };
        let (owner, name, descriptor) = machine.exception_member(index)?;
        Ok((name == "close" && descriptor == "()V" && machine.is_auto_closeable(owner))
            .then_some(index))
    }

    fn after_prefix(&self, block: usize, consumed: usize) -> Option<usize> {
        let &[next] = self.graph.blocks[block].successors.as_slice() else {
            return None;
        };
        match self.block_instructions(block).get(consumed..)? {
            [] => Some(next),
            [jump] if matches!(jump.opcode, 0xa7 | 0xc8) => Some(next),
            _ => None,
        }
    }

    fn block_instructions(&self, block: usize) -> &[Instruction] {
        &self.instructions[self.graph.blocks[block].instructions.clone()]
    }

    fn allocates_nonnull(
        &self,
        block: usize,
        machine: &Machine<'_, '_>,
    ) -> Result<bool, StructureError> {
        let [prefix @ .., invoke, _store] = self.block_instructions(block) else {
            return Ok(false);
        };
        if invoke.opcode != 0xb7 {
            return Ok(false);
        }
        let Some(index) = invocation_index(invoke) else {
            return Ok(false);
        };
        let (owner, method, _) = machine.exception_member(index)?;
        let Some(start) = prefix.iter().rposition(|instruction| instruction.opcode == 0xbb)
        else {
            return Ok(false);
        };
        let [allocation, duplicate, arguments @ ..] = &prefix[start..] else {
            return Ok(false);
        };
        let Operand::Constant(class) = allocation.operand else {
            return Ok(false);
        };
        Ok(method == "<init>"
            && machine.exception_class(class)? == owner
            && duplicate.opcode == 0x59
            && arguments.iter().all(|instruction| matches!(instruction.opcode, 0x01..=0x2d)))
    }

    pub(super) fn exception_range(
        &mut self,
        block: usize,
        region: Region<'_, '_, '_>,
        range: &mut Range<usize>,
    ) -> Result<(), StructureError> {
        if let Some(cleanup) = self.exceptions.finally_range(region.exception_arm, block) {
            *range = cleanup;
            return Ok(());
        }
        range.start += usize::from(self.exceptions.skips_binding(block));
        range.start += self.exceptions.cleanup_prefix(block);
        if let Some(split) = self.exceptions.return_split(region.exception_arm, block) {
            if mem::replace(&mut self.emitted[split], true) {
                return Err(self.unstructured(split));
            }
            range.end = self.graph.blocks[split].instructions.end;
        }
        if let Some(end) = self.exceptions.monitor_acquisition_end(block) {
            if !(range.start..range.end).contains(&end) {
                return Err(self.unstructured(block));
            }
            range.end = end;
        }
        Ok(())
    }
}

fn throwable_catch<'r>(
    region: &'r ProtectedRegion,
    machine: &Machine<'_, '_>,
) -> Result<Option<&'r Catch>, StructureError> {
    let [catch] = region.catches.as_slice() else {
        return Ok(None);
    };
    let &[exception] = catch.alternatives.as_slice() else {
        return Ok(None);
    };
    Ok((region.finally.is_none() && machine.exception_class(exception)? == "java/lang/Throwable")
        .then_some(catch))
}

fn invocation_index(instruction: &Instruction) -> Option<u16> {
    match instruction.operand {
        Operand::Constant(index) | Operand::InvokeInterface { index, .. } => Some(index),
        _ => None,
    }
}

fn is_slot_write(instruction: &Instruction, slot: u16) -> bool {
    matches!(instruction.opcode, 0x36..=0x4e | 0x84) && local_touches(instruction, slot)
}
