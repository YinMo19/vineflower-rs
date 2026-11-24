// Copyright 2000-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

mod resource_exits;

use std::{mem, ops::Range};

use crate::bytecode::{Instruction, Operand};
use crate::lift::{Effect, Machine};
use crate::source_text::Document;

use super::protected::{
    ArmId, Catch, ExceptionId, Legacy, LegacyExit, Monitor, ProtectedRegion, cleanup_locals,
    local_touches, reference_load, reference_store,
};
use super::{Emitter, Line, Region, StructureError};

struct Resource {
    acquisition: usize,
    reference_prefix: Option<usize>,
    slot: u16,
    body_stop: Option<usize>,
    exit: ResourceExit,
    skipped: Vec<usize>,
    redirects: Vec<(usize, ExceptionRedirect)>,
    fulfilled_returns: Vec<usize>,
    epilogue: Option<(usize, u32)>,
}

#[derive(Clone, Copy)]
enum ResourceExit {
    Continue(Option<usize>),
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
    Continue { target: usize, arm: ArmId },
    Return { recipient: ExceptionId, value: ReturnValue },
    ReturnAtEdge { transfer: usize, arm: ArmId },
    ReturnSpill { store: usize, arm: ArmId },
}

struct NormalExits {
    close: usize,
    stop: Option<usize>,
    exit: ResourceExit,
    redirects: Vec<(usize, ExceptionRedirect)>,
    terminal_blocks: Vec<usize>,
    fulfilled_returns: Vec<usize>,
}

struct ClosePattern {
    slot: u16,
    nullable: bool,
    member: u16,
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
    pub(super) fn redirected_exception_block<'a, 'c>(
        &mut self,
        block: usize,
        region: Region<'_, 'a, 'c>,
        machine: &mut Machine<'a, 'c>,
        depth: usize,
        pending: &mut Vec<u32>,
    ) -> Result<Option<usize>, StructureError> {
        match self.exception_redirects.get(&block).copied() {
            None | Some(ExceptionRedirect::ReturnSpill { .. }) => Ok(Some(block)),
            Some(ExceptionRedirect::Continue { target, arm }) if region.exception_arm == Some(arm) => {
                Ok(Some(target))
            }
            Some(ExceptionRedirect::ReturnAtEdge { transfer, arm }) if region.exception_arm == Some(arm) => {
                self.emit_resource_return_transfer(transfer, machine, depth, pending)?;
                Ok(None)
            }
            _ => Err(self.unstructured(block)),
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
        let mut reaches_join = if shape.finally.is_none()
            && let Some(reaches) =
                self.emit_try_with_monitor_departure(clauses, scope, machine, depth + 1)?
        {
            reaches
        } else {
            self.scoped_arm(
                clauses.start,
                scope.exception(clauses.join, clauses.body, Some(machine)),
                machine,
                depth + 1,
            )?
        };
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
                if let Some(&target) = branch.loop_targets.iter().find(|&&target| {
                    region.loop_transfer(target).is_none()
                }) {
                    return Err(self.unstructured(target));
                }
                if let Some(exit) = branch.shared_return
                    && !self.exceptions.contains(region.exception_arm, exit.block)
                {
                    return Err(self.unstructured(exit.block));
                }
                let cleanup_start = self.lines.len();
                if finally.start() != branch.entry
                    && mem::replace(&mut self.emitted[finally.start()], true)
                {
                    return Err(self.unstructured(finally.start()));
                }
                let reaches_tail = self.region_with_offsets(
                    branch.entry,
                    region
                        .exception(branch.tail, finally.arm, None)
                        .with_exception_layout(self.layout.containing_loop(branch.entry)),
                    &mut body,
                    depth + 1,
                    &mut offsets,
                )?;
                if reaches_tail != branch.tail.is_some() {
                    return Err(self.unstructured(branch.entry));
                }
                if let Some(exit) = branch.shared_return {
                    let block = &self.graph.blocks[exit.block];
                    let start = self.offset(exit.block);
                    let last = &self.instructions[block.instructions.end - 1];
                    let range = start..last.offset + last.len;
                    let Some(line) = self.lines[cleanup_start..]
                        .iter_mut()
                        .find(|line| line.offsets.iter().any(|offset| range.contains(offset)))
                    else {
                        return Err(self.unstructured(exit.block));
                    };
                    // The folded transfer belongs to the first statement of
                    // the return path, not to the preceding case statement.
                    let jump = &self.instructions[exit.jump];
                    line.offsets.splice(..0, jump.offset..jump.offset + jump.len);
                    if reaches_join
                        && let Some(next) = branch.continuation
                    {
                        let tail = &self.graph.blocks[next].instructions;
                        let prefix = self.exceptions.cleanup_prefix(next);
                        if prefix > 0
                            && let [jump] = &self.instructions[tail.start + prefix..tail.end]
                            && matches!(jump.opcode, 0xa7 | 0xc8)
                        {
                            // The normal copy's transfer maps to the
                            // statement following the finally.
                            pending.extend(jump.offset..jump.offset + jump.len);
                        }
                    }
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
                if let Some(overriding) = finally.overriding_return() {
                    let [Some(&ExceptionRedirect::Continue { target: normal, arm }),
                         Some(&ExceptionRedirect::Continue { target: exceptional, arm: other })] =
                        [self.exception_redirects.get(&overriding.normal_close),
                         self.exception_redirects.get(&overriding.exceptional_close)]
                    else {
                        return Err(StructureError::ExceptionHandlers);
                    };
                    if normal != exceptional || arm != other || region.exception_arm != Some(arm)
                        || !reaches_join
                        || self.exceptions.at_start(Some(finally.arm), terminal).is_some()
                        || mem::replace(&mut self.emitted[terminal], true)
                    {
                        return Err(self.unstructured(terminal));
                    }
                    let lifted = self.lift_block(terminal, &mut body, cleanup_scope, depth + 1, offsets)?;
                    if !matches!(lifted.effect, Effect::None) {
                        return Err(self.unstructured(terminal));
                    }
                    // The Java return supplies the saved value before the
                    // enclosing resource closes. Its opcode belongs to the
                    // overriding outer finally, so only map the value here.
                    let Effect::Return(Some(mut value)) = body.step(&self.instructions[overriding.transfer])?
                    else {
                        return Err(self.unstructured(terminal));
                    };
                    let mut offsets = lifted.offsets;
                    for statement in body.take_prelude() {
                        self.push(depth + 1, statement, mem::take(&mut offsets));
                    }
                    value.surround("return ", ";");
                    self.push(depth + 1, value, offsets);
                    continuation = Some(overriding.normal_close);
                } else {
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
                }
            } else if finally.branched().is_none_or(|branch| branch.tail.is_some()) {
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
        if let Some(departure) = monitor.departure
            && !region
                .label_scope()
                .is_some_and(|scope| scope.owns_monitor_departure(shape.body, departure))
        {
            return Err(self.unstructured(departure.source));
        }
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
        let reaches = if let Some(reaches) = self.emit_monitor_with_finally_departure(
            shape,
            monitor.plan.acquisition,
            region,
            machine,
            depth + 1,
        )? {
            reaches
        } else {
            self.scoped_arm(
                shape.start,
                region.exception(shape.join, shape.body, Some(machine)),
                machine,
                depth + 1,
            )?
        };
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
            LegacyExit::Continue(next) => ResourceExit::Continue(Some(next)),
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
                body_stop: shape.join,
                exit,
                skipped,
                redirects: Vec::new(),
                fulfilled_returns: Vec::new(),
                epilogue: None,
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

    fn enclosing_resource_continuation(
        &self,
        region: Region<'_, '_, '_>,
        landing: usize,
    ) -> Option<ExceptionRedirect> {
        match self.exception_redirects.get(&landing).copied()? {
            redirect @ ExceptionRedirect::Continue { arm, .. }
                if region.exception_arm == Some(arm) && self.emitted[landing] => Some(redirect),
            _ => None,
        }
    }

    fn emit_resource<'a, 'c>(
        &mut self,
        shape: &ProtectedRegion,
        resource: Resource,
        region: Region<'_, 'a, 'c>,
        machine: &mut Machine<'a, 'c>,
        depth: usize,
    ) -> Result<Option<usize>, StructureError> {
        for landing in resource.fulfilled_returns {
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
                let enclosing = resource.body_stop
                    .filter(|&stop| next == Some(stop))
                    .and_then(|stop| {
                        self.enclosing_resource_continuation(region, stop)
                            .map(|redirect| (stop, redirect))
                    });
                if resource.body_stop.is_some_and(|stop| {
                    enclosing.is_none() && self.exception_redirects.contains_key(&stop)
                }) || resource.redirects.iter().any(|(entry, _)| self.exception_redirects.contains_key(entry))
                {
                    return Err(StructureError::ExceptionHandlers);
                }
                // The child stops at the exact enclosing close entrance.
                // Only the enclosing arm may follow its redirect beyond that entrance.
                if let Some((stop, _)) = enclosing {
                    self.exception_redirects.remove(&stop);
                }
                for &(entry, transfer) in &resource.redirects {
                    self.exception_redirects.insert(entry, transfer);
                }
                let reaches_stop = self.scoped_arm(
                    shape.start,
                    region.exception(resource.body_stop, shape.body, Some(machine)),
                    machine,
                    depth + 1,
                );
                let mut unfulfilled = false;
                for (entry, redirect) in resource.redirects {
                    let remaining = self.exception_redirects.remove(&entry);
                    unfulfilled |= matches!(redirect, ExceptionRedirect::Return { .. })
                        && remaining.is_some();
                }
                if let Some((stop, redirect)) = enclosing {
                    self.exception_redirects.insert(stop, redirect);
                }
                if reaches_stop? != next.is_some() || unfulfilled {
                    return Err(self.unstructured(shape.start));
                }
                next
            }
            ResourceExit::Return { spill, transfer } => {
                self.emit_resource_return(shape, spill, transfer, region, machine, depth + 1)?;
                None
            }
            ResourceExit::DelegateReturn { recipient, value } => {
                let landing = resource.body_stop.ok_or(StructureError::ExceptionHandlers)?;
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
        if let Some(epilogue) = resource.epilogue {
            self.resource_epilogue = Some(epilogue);
        }
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
        let mut offsets = tail.offsets;
        self.emit_resource_return_transfer(transfer, &mut body, depth, &mut offsets)?;
        Self::check_scope(body, baseline, self.offset(spill))
    }

    fn emit_resource_return_transfer(
        &mut self,
        transfer: usize,
        machine: &mut Machine<'_, '_>,
        depth: usize,
        offsets: &mut Vec<u32>,
    ) -> Result<(), StructureError> {
        let instruction = &self.instructions[transfer];
        let Effect::Return(Some(mut value)) = machine.step(instruction)? else {
            return Err(StructureError::ExceptionHandlers);
        };
        if !machine.stack_is_empty() {
            return Err(StructureError::StackJoin { offset: instruction.offset });
        }
        for statement in machine.take_prelude() {
            self.push(depth, statement, mem::take(offsets));
        }
        offsets.extend(instruction.offset..instruction.offset + instruction.len);
        value.surround("return ", ";");
        self.push(depth, value, mem::take(offsets));
        Ok(())
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
        let pattern = ClosePattern { slot, nullable, member: close_method };
        let Some(normal) = (if shape.split_resource_exits.is_empty() {
            self.prove_single_resource_exit(id, shape, machine, primary.start, pattern, &mut skipped)?
        } else {
            self.prove_split_resource_exits(id, region, machine, primary.start, pattern, &mut skipped)?
        }) else {
            return Ok(None);
        };
        let normal_close = normal.close;
        let ambient = &self.graph.blocks[normal_close].exception_successors;
        if self.graph.blocks[suppression.start].exception_successors != *ambient
            || self.graph.blocks[rethrow].exception_successors != *ambient
            || !self.graph.blocks[exceptional_close]
                .exception_successors
                .iter()
                .copied()
                .filter(|&handler| handler != suppression.start)
                .eq(ambient.iter().copied())
            || !self.exceptions.matches_dispatch(suppression.start, normal_close, None)
            || !self.exceptions.matches_dispatch(rethrow, normal_close, None)
            || !self.exceptions.matches_dispatch(exceptional_close, normal_close, Some(suppression.start))
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
                        && !(normal.terminal_blocks.contains(&block)
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
            body_stop: normal.stop,
            exit: normal.exit,
            skipped,
            redirects: normal.redirects,
            fulfilled_returns: normal.fulfilled_returns,
            epilogue: self.resource_epilogue_jump(shape, region, normal_close, normal.exit, nullable),
        }))
    }

    fn resource_epilogue_jump(
        &self,
        shape: &ProtectedRegion,
        region: Region<'_, '_, '_>,
        close: usize,
        exit: ResourceExit,
        nullable: bool,
    ) -> Option<(usize, u32)> {
        if nullable
            || !shape.split_resource_exits.is_empty()
            || region.exception_arm.is_some()
            || region.loop_header.is_some()
            || region.switch_depth != 0
            || region.stop.is_some()
        {
            return None;
        }
        let ResourceExit::Continue(Some(target)) = exit else {
            return None;
        };
        let [_, _, jump] = self.block_instructions(close) else {
            return None;
        };
        let [returned] = self.block_instructions(target) else {
            return None;
        };
        // Upstream keeps the outgoing goto offset on the method epilogue
        // after removing the unguarded close.
        (matches!(jump.opcode, 0xa7 | 0xc8)
            && returned.opcode == 0xb1
            && self.graph.blocks[target].predecessors == [close]
            && self.graph.blocks[target].exception_predecessors.is_empty())
        .then_some((target, jump.offset))
    }

    fn prove_single_resource_exit(
        &mut self,
        id: ExceptionId,
        shape: &ProtectedRegion,
        machine: &Machine<'_, '_>,
        primary: usize,
        pattern: ClosePattern,
        skipped: &mut Vec<usize>,
    ) -> Result<Option<NormalExits>, StructureError> {
        let Some(entry) = shape.join else { return Ok(None) };
        let Some((close, exit)) = self.match_normal_resource_close(
            entry, pattern.slot, pattern.nullable, pattern.member, machine,
        )? else {
            return Ok(None);
        };
        if entry != close {
            skipped.push(entry);
        }
        skipped.push(close);
        let mut fulfilled_return = None;
        let mut terminal_blocks = Vec::new();
        let exit = match exit {
            CloseExit::Continue(next) => {
                if skipped.contains(&next)
                    || self.layout.local_is_live(self.graph, self.instructions, next, pattern.slot)
                {
                    return Ok(None);
                }
                match self.exception_redirects.get(&next).copied() {
                    Some(ExceptionRedirect::Return { recipient, value }) if recipient == id => {
                        let Some(exit) = self.resource_body_return(shape, entry, close, primary, value)
                        else {
                            return Ok(None);
                        };
                        fulfilled_return = Some(next);
                        exit
                    }
                    _ => ResourceExit::Continue(Some(next)),
                }
            }
            CloseExit::Return { block, transfer, local } => {
                if block != close {
                    if self.graph.blocks[block].predecessors.iter().any(|&pred| pred != entry && pred != close) {
                        return Ok(None);
                    }
                    skipped.push(block);
                    terminal_blocks.push(block);
                }
                let Some(exit) = self.resource_body_return(
                    shape, entry, close, primary, ReturnValue { local, transfer },
                ) else {
                    return Ok(None);
                };
                exit
            }
        };
        Ok(Some(NormalExits {
            close,
            stop: Some(entry),
            exit,
            redirects: Vec::new(),
            terminal_blocks,
            fulfilled_returns: fulfilled_return.into_iter().collect(),
        }))
    }

    fn exclusive_resource_spill(
        &self,
        shape: &ProtectedRegion,
        landing: usize,
        local: cleanup_locals::Local,
    ) -> Option<(usize, usize)> {
        let &[spill] = self.graph.blocks[landing].predecessors.as_slice() else {
            return None;
        };
        let block = &self.graph.blocks[spill];
        let store = block.instructions.end - 1;
        (self.exceptions.contains(Some(shape.body), spill)
            && self.exceptions.at_start(Some(shape.body), spill).is_none()
            && self.exceptions.bypass_cleanup(spill) == spill
            && !self.exceptions.skips_binding(spill)
            && !self.exceptions.skips_instruction(store)
            && self.exceptions.return_split(Some(shape.body), spill).is_none()
            && self.exceptions.cleanup_prefix(spill) == 0
            && self.exceptions.monitor_acquisition_end(spill).is_none()
            && block.successors == [landing]
            && cleanup_locals::store(&self.instructions[store]) == Some(local))
        .then_some((spill, store))
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
        if let Some((spill, _)) = self.exclusive_resource_spill(shape, landing, value.local) {
            return Some(ResourceExit::Return { spill, transfer: value.transfer });
        }
        let predecessors = self.graph.blocks[landing].predecessors.as_slice();

        // If a child closes first, the spill belongs to that child, not
        // the parent. Assign the obligation to the one lexical child whose
        // close edges account for every normal predecessor of this landing.
        let mut children = self.exceptions.children_of(shape.body).filter(|&id| {
            let child = self.exceptions.region(id);
            child.catches.len() == 1
                && child.join.into_iter().chain(child.split_resource_exits.iter().copied()).any(|entry| {
                    entry != landing
                        && self.exceptions.contains(Some(shape.body), entry)
                        && match self.graph.blocks[entry].successors.as_slice() {
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
                })
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
        if let Some(&ExceptionRedirect::ReturnSpill { store, arm }) = self.exception_redirects.get(&block) {
            if region.exception_arm != Some(arm) || range.end != store + 1 || !range.contains(&store) {
                return Err(self.unstructured(block));
            }
            range.end = store;
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
