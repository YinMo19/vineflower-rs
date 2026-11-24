// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use std::{mem, ops::Range};

use crate::bytecode::{Instruction, Operand};
use crate::lift::{Effect, Machine};
use crate::source_text::Document;

use super::protected::{
    Catch, ExceptionId, Legacy, LegacyExit, Monitor, ProtectedRegion, cleanup_locals,
    local_touches, reference_load, reference_store,
};
use super::{Emitter, Line, Region, StructureError};

struct Resource {
    acquisition: usize,
    reference_prefix: Option<usize>,
    slot: u16,
    body_stop: usize,
    exit: ResourceExit,
    skipped: Vec<usize>,
    redirects: Vec<usize>,
    fulfilled_return: Option<usize>,
}

#[derive(Clone, Copy)]
enum ResourceExit {
    Continue(usize),
    Return { spill: usize, transfer: usize },
    DelegateReturn { recipient: ExceptionId, value: ReturnValue },
}

#[derive(Clone, Copy)]
pub(super) struct ReturnValue {
    transfer: usize,
    local: cleanup_locals::Local,
}

#[derive(Clone, Copy)]
pub(super) enum ExceptionRedirect {
    Continue(usize),
    Return { recipient: ExceptionId, value: ReturnValue },
}

enum CloseExit {
    Continue(usize),
    Return {
        block: usize,
        transfer: usize,
        local: cleanup_locals::Local,
    },
}

// Return the header length only when these lines form a single catchless
// resource statement. Independent statements and clauses stay nested.
fn resource_header_length(lines: &[Line], depth: usize) -> Option<usize> {
    let (end, content) = lines.split_last()?;
    let (header, tail) = content.split_first()?;
    if end.depth != depth
        || end.text.as_flat() != "}"
        || !end.offsets.is_empty()
        || header.depth != depth
    {
        return None;
    }
    let header_text = header.text.as_flat();
    let length = if header_text == "try (" && header.offsets.is_empty() {
        let close = tail.iter().position(|line| line.depth <= depth)?;
        if close < 2
            || tail[close].depth != depth
            || tail[close].text.as_flat() != ") {"
            || !tail[close].offsets.is_empty()
            || !tail[..close].iter().all(|line| line.depth == depth + 1)
        {
            return None;
        }
        close + 2
    } else if header_text.starts_with("try (") && header_text.ends_with(") {") {
        1
    } else {
        return None;
    };
    content[length..]
        .iter()
        .all(|line| line.depth > depth)
        .then_some(length)
}

fn split_resource_declaration(line: &mut Line, depth: usize) {
    let end = line.text.as_flat().len() - ") {".len();
    line.text.truncate(end);
    line.text.replace_literal_prefix("try (".len(), "");
    line.text.push(';');
    line.depth = depth;
    line.sequence_boundary = false;
}

fn merge_nested_resource(lines: &mut Vec<Line>, outer: usize, depth: usize) {
    let inner = outer + 1;
    let Some(length) = resource_header_length(&lines[inner..], depth + 1) else {
        return;
    };
    // JLS lowering of multiple resources is precisely this nesting:
    // acquire in declaration order, close in reverse, preserving suppression.
    lines.pop();
    let boundary = lines[outer].sequence_boundary;
    split_resource_declaration(&mut lines[outer], depth + 1);
    let body = if length == 1 {
        split_resource_declaration(&mut lines[inner], depth + 1);
        lines.insert(inner + 1, Line::new(depth, ") {", Vec::new()));
        inner + 2
    } else {
        lines.remove(inner);
        let body = inner + length - 1;
        for line in &mut lines[inner..body] {
            line.depth -= 1;
        }
        body
    };
    for line in &mut lines[body..] {
        line.depth -= 1;
    }
    let mut header = Line::new(depth, "try (", Vec::new());
    header.sequence_boundary = boundary;
    lines.insert(outer, header);
}

impl Emitter<'_> {
    pub(super) fn redirected_exception_block(&self, block: usize) -> Result<usize, StructureError> {
        match self.exception_redirects.get(&block) {
            None => Ok(block),
            Some(&ExceptionRedirect::Continue(next)) => Ok(next),
            Some(ExceptionRedirect::Return { .. }) => Err(self.unstructured(block)),
        }
    }

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
        if let Some(legacy) = &shape.legacy_resource {
            return self.emit_legacy_resource(shape, legacy, region, machine, depth);
        }
        if let Some(resource) = self.prove_resource(id, shape, region, machine, depth)? {
            return self.emit_resource(shape, resource, region, machine, depth);
        }
        if !shape.split_resource_exits.is_empty() {
            return Err(StructureError::ExceptionHandlers);
        }
        let (clauses, scope) = if let Some(inner) = exceptions.catches_of_finally(shape) {
            (
                inner,
                region.exception(shape.join, shape.body, Some(machine)),
            )
        } else {
            (shape, region)
        };
        let body_lines = self.lines.len();
        self.syntax(depth, "try {");
        let mut reaches_join = self.scoped_arm(
            clauses.start,
            scope.exception(clauses.join, clauses.body, Some(machine)),
            machine,
            depth + 1,
        )?;
        // If the entire protected body is one verified resource statement,
        // the surrounding catch/finally clauses are its Java clauses. The
        // acquisition and both close paths remain inside that same scope.
        self.fuse_resource_wrapper(body_lines, depth);
        for catch in &clauses.catches {
            let store = &self.instructions[self.graph.blocks[catch.start].instructions.start];
            let mut body = machine.clone();
            let (types, name) = match catch.alternatives.as_slice() {
                &[single] => body.bind_caught_exception(single, store)?,
                types => {
                    // The verifier supplies the handler's actual local type;
                    // using an arbitrary alternative can incorrectly narrow
                    // later expressions referring to the catch parameter.
                    let common = body
                        .caught_exception_stack_type(store.offset)?
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
            let mut header = Document::from(format!("}} catch ({types} "));
            header.append(name);
            header.push_str(") {");
            self.push(
                depth,
                header,
                (store.offset..store.offset + store.len).collect(),
            );
            if self.region(
                catch.start,
                scope
                    .exception(clauses.join, catch.arm, None)
                    .with_exception_layout(self.layout.containing_loop(catch.start)),
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
            for &(returned, stored) in finally.spill_offsets() {
                let returned = self.instructions[returned].offset;
                let store = &self.instructions[stored];
                for line in &mut self.lines[body_lines..] {
                    if let Some(at) = line.offsets.iter().position(|&offset| offset == returned) {
                        line.offsets
                            .splice(at..=at, store.offset..store.offset + store.len);
                        break;
                    }
                }
            }
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
                    region
                        .exception(Some(finally.block()), finally.arm, None)
                        .with_exception_layout(self.layout.containing_loop(branch.entry)),
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
            let terminal = finally.block();
            let cleanup_scope = region.exception(None, finally.arm, None);
            if let Some(copies) = finally.terminal_copies() {
                for &copy in copies {
                    if !self.exceptions.contains(region.exception_arm, copy)
                        || mem::replace(&mut self.emitted[copy], true)
                    {
                        return Err(self.unstructured(copy));
                    }
                }
                if self.region_with_offsets(
                    terminal,
                    cleanup_scope.with_exception_layout(self.layout.containing_loop(terminal)),
                    &mut body,
                    depth + 1,
                    &mut offsets,
                )? {
                    return Err(self.unstructured(terminal));
                }
                continuation = None;
            } else {
                if mem::replace(&mut self.emitted[terminal], true) {
                    return Err(self.unstructured(terminal));
                }
                let cleanup = self.lift_block(terminal, &mut body, cleanup_scope, depth + 1, offsets)?;
                if !matches!(cleanup.effect, Effect::None) {
                    return Err(self.unstructured(terminal));
                }
            }
            Self::check_scope(body, machine, self.offset(finally.block()))?;
        }
        self.syntax(depth, "}");
        Ok(if reaches_join { continuation } else { None })
    }

    fn fuse_resource_wrapper(&mut self, wrapper: usize, depth: usize) {
        if resource_header_length(&self.lines[wrapper + 1..], depth + 1).is_none() {
            return;
        }
        self.lines.pop();
        self.lines.remove(wrapper);
        for line in &mut self.lines[wrapper..] {
            line.depth -= 1;
        }
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
        let mut lock = machine.take_monitor_lock(enter)?;
        let mut offsets = mem::take(pending);
        for statement in machine.take_prelude() {
            self.push(depth, statement, mem::take(&mut offsets));
        }
        offsets.extend(enter.offset..enter.offset + enter.len);
        lock.surround("synchronized (", ") {");
        self.push(depth, lock, offsets);
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
            self.push(
                depth,
                Document::from("}"),
                vec![self.instructions[index].offset],
            );
        } else {
            self.syntax(depth, "}");
        }
        Ok(if reaches { shape.join } else { None })
    }

    fn emit_legacy_resource<'a, 'c>(
        &mut self,
        shape: &ProtectedRegion,
        legacy: &Legacy,
        region: Region<'_, 'a, 'c>,
        machine: &mut Machine<'a, 'c>,
        depth: usize,
    ) -> Result<Option<usize>, StructureError> {
        let acquisition = self
            .resource_declaration(legacy.acquisition, legacy.slot, depth, machine, 2)
            .ok_or_else(|| self.unstructured(shape.start))?;
        let mut terminal = None;
        let exit = match legacy.exit {
            LegacyExit::Continue(next) => ResourceExit::Continue(next),
            LegacyExit::Return {
                spill,
                block,
                transfer,
            } => {
                if self.exceptions.at_start(Some(shape.body), spill).is_some()
                    || self.exceptions.cleanup_prefix(spill) != 0
                    || self.exceptions.skips_binding(spill)
                    || self.exceptions.monitor_acquisition_end(spill).is_some()
                    || self
                        .exceptions
                        .skips_instruction(self.graph.blocks[spill].instructions.end - 1)
                {
                    return Err(self.unstructured(spill));
                }
                terminal = Some(block);
                ResourceExit::Return { spill, transfer }
            }
        };
        let mut skipped = Vec::new();
        for block in self.exceptions.arm_blocks(legacy.arm).chain(terminal) {
            if self.emitted[block]
                || self.exceptions.cleanup_prefix(block) != 0
                || (!self.exceptions.contains(region.exception_arm, block)
                    && !matches!(exit, ResourceExit::Return { transfer, .. }
                        if self.graph.blocks[block].instructions.contains(&transfer)
                            && self.graph.blocks[block].exception_successors.is_empty()))
            {
                return Err(self.unstructured(block));
            }
            skipped.push(block);
        }
        self.emit_resource(
            shape,
            Resource {
                acquisition,
                reference_prefix: None,
                slot: legacy.slot,
                body_stop: shape.join.ok_or(StructureError::ExceptionHandlers)?,
                exit,
                skipped,
                redirects: Vec::new(),
                fulfilled_return: None,
            },
            region,
            machine,
            depth,
        )
    }

    fn resource_declaration(
        &self,
        block: usize,
        slot: u16,
        depth: usize,
        machine: &Machine<'_, '_>,
        suffix: usize,
    ) -> Option<usize> {
        let index = self.lines.len().checked_sub(1)?;
        let instructions = self.block_instructions(block);
        let store = instructions.get(instructions.len().checked_sub(suffix + 1)?)?;
        let line = &self.lines[index];
        let (ty, name) = machine.resource_local(slot)?;
        let text = line.text.as_flat();
        (line.depth == depth
            && line.offsets.contains(&store.offset)
            && text.ends_with(';')
            && text
                .strip_prefix(&ty)
                .and_then(|text| text.strip_prefix(' '))
                .and_then(|text| text.strip_prefix(name))
                .is_some_and(|text| text.starts_with(" = ")))
        .then_some(index)
    }

    fn resource_reference_prefix(
        &self,
        shape: &ProtectedRegion,
        predecessor: usize,
        alias: u16,
        declaration: usize,
        machine: &Machine<'_, '_>,
    ) -> Option<usize> {
        let [.., load, _store] = self.block_instructions(predecessor) else {
            return None;
        };
        let source = reference_load(load)?;
        let (name, parameter) = machine.existing_resource_local(source, alias)?;
        let text = self.lines[declaration].text.as_flat().strip_suffix(';')?;
        let (left, right) = text.rsplit_once(" = ")?;
        if right != name
            || !self.graph.blocks[shape.start].exception_predecessors.is_empty()
            || self.exceptions.arm_blocks(shape.body).any(|block| {
                self.block_instructions(block).iter().any(|op| local_touches(op, alias))
            })
        {
            return None;
        }
        // The alias is only a snapshot of the original variable. In source
        // it can disappear only when that variable is effectively final.
        let mut stores = self.instructions.iter().filter(|op| is_slot_write(op, source));
        match (parameter, stores.next()) {
            (true, None) => {}
            (false, Some(store)) if store.offset < load.offset && stores.next().is_none() => {}
            _ => return None,
        }
        Some(left.len() + " = ".len())
    }

    fn emit_resource<'a, 'c>(
        &mut self,
        shape: &ProtectedRegion,
        resource: Resource,
        region: Region<'_, 'a, 'c>,
        machine: &mut Machine<'a, 'c>,
        depth: usize,
    ) -> Result<Option<usize>, StructureError> {
        if let Some(landing) = resource.fulfilled_return {
            if !matches!(
                self.exception_redirects.remove(&landing),
                Some(ExceptionRedirect::Return { .. })
            ) {
                return Err(self.unstructured(landing));
            }
        }
        let line = &mut self.lines[resource.acquisition];
        if let Some(prefix) = resource.reference_prefix {
            line.text.replace_literal_prefix(prefix, "");
            line.sequence_boundary = true;
        }
        line.text.pop(); // Verified declaration terminator.
        line.text.surround("try (", ") {");
        for block in resource.skipped {
            self.emitted[block] = true;
        }
        let next = match resource.exit {
            ResourceExit::Continue(next) => {
                if self.exception_redirects.contains_key(&resource.body_stop)
                    || resource
                        .redirects
                        .iter()
                        .any(|entry| self.exception_redirects.contains_key(entry))
                {
                    return Err(StructureError::ExceptionHandlers);
                }
                for &entry in &resource.redirects {
                    self.exception_redirects
                        .insert(entry, ExceptionRedirect::Continue(resource.body_stop));
                }
                let reaches_stop = self.scoped_arm(
                    shape.start,
                    region.exception(Some(resource.body_stop), shape.body, Some(machine)),
                    machine,
                    depth + 1,
                );
                for entry in resource.redirects {
                    self.exception_redirects.remove(&entry);
                }
                if !reaches_stop? {
                    return Err(self.unstructured(shape.start));
                }
                Some(next)
            }
            ResourceExit::Return { spill, transfer } => {
                self.emit_resource_return(shape, spill, transfer, region, machine, depth + 1)?;
                None
            }
            ResourceExit::DelegateReturn { recipient, value } => {
                let landing = resource.body_stop;
                if self.exception_redirects.contains_key(&landing) {
                    return Err(self.unstructured(landing));
                }
                self.exception_redirects.insert(
                    landing,
                    ExceptionRedirect::Return { recipient, value },
                );
                let reaches = self.scoped_arm(
                    shape.start,
                    region.exception(Some(landing), shape.body, Some(machine)),
                    machine,
                    depth + 1,
                );
                let unfulfilled = self.exception_redirects.remove(&landing).is_some();
                if reaches? || unfulfilled {
                    return Err(self.unstructured(landing));
                }
                None
            }
        };
        merge_nested_resource(&mut self.lines, resource.acquisition, depth);
        self.syntax(depth, "}");
        machine.forget_resource_local(resource.slot);
        Ok(next)
    }

    fn emit_resource_return<'a, 'c>(
        &mut self,
        shape: &ProtectedRegion,
        spill: usize,
        transfer: usize,
        region: Region<'_, 'a, 'c>,
        baseline: &Machine<'a, 'c>,
        depth: usize,
    ) -> Result<(), StructureError> {
        let scope = region.exception(Some(spill), shape.body, Some(baseline));
        let mut body = baseline.clone();
        let mut offsets = Vec::new();
        if !self.region_with_offsets(shape.start, scope, &mut body, depth, &mut offsets)?
            || mem::replace(&mut self.emitted[spill], true)
        {
            return Err(self.unstructured(spill));
        }
        let range = &self.graph.blocks[spill].instructions;
        let tail = self.lift_range(
            spill,
            range.start..range.end - 1,
            &mut body,
            scope,
            depth,
            offsets,
        )?;
        if !matches!(tail.effect, Effect::None) {
            return Err(self.unstructured(spill));
        }
        let transfer = &self.instructions[transfer];
        let Effect::Return(Some(mut value)) = body.step(transfer)? else {
            return Err(self.unstructured(spill));
        };
        let mut offsets = tail.offsets;
        for statement in body.take_prelude() {
            self.push(depth, statement, mem::take(&mut offsets));
        }
        offsets.extend(transfer.offset..transfer.offset + transfer.len);
        value.surround("return ", ";");
        self.push(depth, value, offsets);
        Self::check_scope(body, baseline, self.offset(spill))
    }

    // javac's modern resource lowering has two close paths. The exception
    // path closes under a Throwable handler which suppresses on the original
    // exception, then rethrows that exact object. Verify the local identities,
    // exception coverage, and every edge in those paths before hiding them.
    fn prove_resource(
        &mut self,
        id: ExceptionId,
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
        let Some(acquisition) = self.resource_declaration(predecessor, slot, depth, machine, 0)
        else {
            return Ok(None);
        };
        if self.graph.blocks[predecessor].successors != [shape.start]
            || !self.exceptions.contains(region.exception_arm, predecessor)
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
        let Some(inner) = self
            .exceptions
            .at_start(Some(primary.arm), exceptional_close)
        else {
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
                != (
                    "java/lang/Throwable",
                    "addSuppressed",
                    "(Ljava/lang/Throwable;)V",
                )
            || self.after_prefix(suppression.start, 4) != Some(rethrow)
            || !self
                .exceptions
                .arm_blocks(primary.arm)
                .all(|block| skipped.contains(&block))
        {
            return Ok(None);
        }

        let nullable = null_rethrow.is_some();
        if !nullable && !self.allocates_nonnull(predecessor, machine)? {
            return Ok(None);
        }
        let Some((normal_close, close_exit)) =
            self.match_normal_resource_close(normal_cleanup, slot, nullable, close_method, machine)?
        else {
            return Ok(None);
        };
        if normal_cleanup != normal_close {
            skipped.push(normal_cleanup);
        }
        skipped.push(normal_close);
        let mut fulfilled_return = None;
        let mut return_transfer = None;
        let exit = match close_exit {
            CloseExit::Continue(next) => {
                if skipped.contains(&next)
                    || self
                        .layout
                        .local_is_live(self.graph, self.instructions, next, slot)
                {
                    return Ok(None);
                }
                match self.exception_redirects.get(&next).copied() {
                    Some(ExceptionRedirect::Return { recipient, value }) if recipient == id => {
                        let Some(exit) = self.resource_body_return(
                            shape,
                            normal_cleanup,
                            normal_close,
                            primary.start,
                            value,
                        ) else {
                            return Ok(None);
                        };
                        fulfilled_return = Some(next);
                        exit
                    }
                    _ => ResourceExit::Continue(next),
                }
            }
            CloseExit::Return {
                block,
                transfer,
                local,
            } => {
                if block != normal_close
                    && self.graph.blocks[block]
                        .predecessors
                        .iter()
                        .any(|pred| !skipped.contains(pred))
                {
                    return Ok(None);
                }
                if block != normal_close {
                    skipped.push(block);
                }
                return_transfer = Some(transfer);
                let Some(exit) = self.resource_body_return(
                    shape,
                    normal_cleanup,
                    normal_close,
                    primary.start,
                    ReturnValue { local, transfer },
                ) else {
                    return Ok(None);
                };
                exit
            }
        };

        let ambient = &self.graph.blocks[normal_close].exception_successors;
        let mut body_stop = normal_cleanup;
        let mut redirects = Vec::new();
        if !shape.split_resource_exits.is_empty() {
            let ResourceExit::Continue(next) = exit else {
                return Ok(None);
            };
            if self.exceptions.contains(Some(shape.body), next)
                || !self.exceptions.contains(region.exception_arm, next)
                || self.exceptions.at_start(region.exception_arm, next).is_some()
                || self.exceptions.bypass_cleanup(next) != next
                || self.layout.loops[next].is_some()
                || region.loop_transfer(next).is_some()
                || !self.graph.blocks[next].exception_predecessors.is_empty()
            {
                return Ok(None);
            }
            for &entry in &shape.split_resource_exits {
                let Some((close, CloseExit::Continue(target))) =
                    self.match_normal_resource_close(entry, slot, nullable, close_method, machine)?
                else {
                    return Ok(None);
                };
                if next != target
                    || skipped.contains(&entry)
                    || skipped.contains(&close)
                    || self.graph.blocks[close].exception_successors != *ambient
                    || self.exceptions.at_start(region.exception_arm, entry).is_some()
                    || self.exceptions.at_start(region.exception_arm, close).is_some()
                {
                    return Ok(None);
                }
                if entry != close {
                    skipped.push(entry);
                }
                skipped.push(close);
                redirects.push(entry);
            }
            redirects.push(normal_cleanup);
            if redirects.iter().any(|&entry| {
                self.graph.blocks[entry]
                    .predecessors
                    .iter()
                    .any(|&pred| !self.exceptions.contains(Some(shape.body), pred))
            }) {
                return Ok(None);
            }
            body_stop = next;
        }
        if self.graph.blocks[suppression.start].exception_successors != *ambient
            || self.graph.blocks[rethrow].exception_successors != *ambient
            || !self.graph.blocks[exceptional_close]
                .exception_successors
                .iter()
                .copied()
                .filter(|&handler| handler != suppression.start)
                .eq(ambient.iter().copied())
            || self
                .exceptions
                .at_start(region.exception_arm, normal_cleanup)
                .is_some()
            || self
                .exceptions
                .at_start(region.exception_arm, normal_close)
                .is_some()
            || skipped.iter().any(|&block| {
                self.emitted[block]
                    || self.exceptions.bypass_cleanup(block) != block
                    || self.exceptions.cleanup_prefix(block) != 0
                    || (!self.exceptions.contains(region.exception_arm, block)
                        && !return_transfer.is_some_and(|transfer|
                            self.graph.blocks[block].instructions.contains(&transfer)
                                && self.graph.blocks[block].exception_successors.is_empty()))
                    || (!self.graph.blocks[block].exception_predecessors.is_empty()
                        && !self.exceptions.contains(Some(primary.arm), block))
                    || self.graph.blocks[block].predecessors.iter().any(|pred| {
                        !skipped.contains(pred)
                            && !self.exceptions.contains(Some(shape.body), *pred)
                    })
            })
            || self.exceptions.arm_blocks(shape.body).any(|block| {
                self.block_instructions(block).iter().any(|instruction| {
                    matches!(instruction.opcode, 0xac..=0xb1) || is_slot_write(instruction, slot)
                })
            })
        {
            return Ok(None);
        }
        Ok(Some(Resource {
            acquisition,
            reference_prefix: self.resource_reference_prefix(
                shape, predecessor, slot, acquisition, machine,
            ),
            slot,
            body_stop,
            exit,
            skipped,
            redirects,
            fulfilled_return,
        }))
    }

    fn resource_body_return(
        &mut self,
        shape: &ProtectedRegion,
        landing: usize,
        close: usize,
        primary: usize,
        value: ReturnValue,
    ) -> Option<ResourceExit> {
        if self.protected_resource_slot_overlap(value.local, close, primary) {
            return None;
        }
        let predecessors = self.graph.blocks[landing].predecessors.as_slice();
        if let &[spill] = predecessors {
            let block = &self.graph.blocks[spill];
            let store = block.instructions.end - 1;
            if self.exceptions.contains(Some(shape.body), spill)
                && self.exceptions.at_start(Some(shape.body), spill).is_none()
                && !self.exceptions.skips_binding(spill)
                && !self.exceptions.skips_instruction(store)
                && self.exceptions.cleanup_prefix(spill) == 0
                && self.exceptions.monitor_acquisition_end(spill).is_none()
                && block.successors == [landing]
                && cleanup_locals::store(&self.instructions[store]) == Some(value.local)
            {
                return Some(ResourceExit::Return { spill, transfer: value.transfer });
            }
        }

        // If a child closes first, the spill belongs to that child, not
        // the parent. Assign the obligation to the one lexical child whose
        // close edges account for every normal predecessor of this landing.
        let mut children = self.exceptions.children_of(shape.body).filter(|&id| {
            let child = self.exceptions.region(id);
            let Some(entry) = child.join else { return false };
            if child.catches.len() != 1
                || !child.split_resource_exits.is_empty()
                || entry == landing
                || !self.exceptions.contains(Some(shape.body), entry)
            {
                return false;
            }
            match self.graph.blocks[entry].successors.as_slice() {
                &[next] => next == landing && predecessors == [entry],
                &[next, close] => {
                    next == landing
                        && self.exceptions.contains(Some(shape.body), close)
                        && self.graph.blocks[close].predecessors == [entry]
                        && self.graph.blocks[close].successors == [landing]
                        && predecessors.len() == 2
                        && predecessors.contains(&entry)
                        && predecessors.contains(&close)
                }
                _ => false,
            }
        });
        let recipient = children.next()?;
        children.next().is_none().then_some(ResourceExit::DelegateReturn { recipient, value })
    }

    fn match_normal_resource_close(
        &self,
        entry: usize,
        slot: u16,
        nullable: bool,
        close_method: u16,
        machine: &Machine<'_, '_>,
    ) -> Result<Option<(usize, CloseExit)>, StructureError> {
        let (close, exit) = if nullable {
            let [load, test] = self.block_instructions(entry) else {
                return Ok(None);
            };
            let &[next, close] = self.graph.blocks[entry].successors.as_slice() else {
                return Ok(None);
            };
            if reference_load(load) != Some(slot)
                || test.opcode != 0xc6
                || self.after_prefix(close, 2) != Some(next)
            {
                return Ok(None);
            }
            (
                close,
                self.resource_return_tail(next, 0)
                    .unwrap_or(CloseExit::Continue(next)),
            )
        } else if let Some(returned) = self.resource_return_tail(entry, 2) {
            (entry, returned)
        } else if let Some(next) = self.after_prefix(entry, 2) {
            (
                entry,
                self.resource_return_tail(next, 0)
                    .unwrap_or(CloseExit::Continue(next)),
            )
        } else {
            return Ok(None);
        };
        Ok((self.close_method(close, slot, machine)? == Some(close_method)).then_some((close, exit)))
    }

    fn resource_return_tail(&self, block: usize, consumed: usize) -> Option<CloseExit> {
        if !self.graph.blocks[block].exception_predecessors.is_empty() {
            return None;
        }
        let [load, transfer] = self.block_instructions(block).get(consumed..)? else {
            return None;
        };
        let local = cleanup_locals::returned(load, transfer)?;
        Some(CloseExit::Return {
            block,
            transfer: self.graph.blocks[block].instructions.end - 1,
            local,
        })
    }

    fn protected_resource_slot_overlap(
        &mut self,
        spill: cleanup_locals::Local,
        normal_close: usize,
        handler: usize,
    ) -> bool {
        // Close receives only the resource; it may not overwrite the spill
        // nor expose it to an outer handler. The original store has no
        // observable value on an exceptional body path (it ran last).
        self.block_instructions(normal_close)[..2]
            .iter()
            .any(|op| spill.touches(op))
            || self.graph.blocks[normal_close]
                .exception_successors
                .iter()
                .copied()
                .any(|target| {
                    // Layout tracks reads by the low slot of each binding.
                    // Include preceding slots for possible category-2 aliases.
                    target == handler
                        || spill.slots().any(|slot| {
                            self.layout
                                .local_is_live(self.graph, self.instructions, target, slot)
                                || slot.checked_sub(1).is_some_and(|previous| {
                                    self.layout.local_is_live(
                                        self.graph,
                                        self.instructions,
                                        target,
                                        previous,
                                    )
                                })
                        })
                })
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
        Ok(
            (name == "close" && descriptor == "()V" && machine.is_auto_closeable(owner))
                .then_some(index),
        )
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
        let Some(start) = prefix
            .iter()
            .rposition(|instruction| instruction.opcode == 0xbb)
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
            && arguments
                .iter()
                .all(|instruction| matches!(instruction.opcode, 0x01..=0x2d)))
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
    Ok(
        (region.finally.is_none() && machine.exception_class(exception)? == "java/lang/Throwable")
            .then_some(catch),
    )
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
