// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.

mod render;

use std::{fmt::Write, ops::Range};

use crate::classfile::LocalVariable;

use super::{
    Bytecode, Code, Instruction, JvmType, KotlinError, Locals, Operand, ScopedLocal, ValueParameter,
    identifier, load_opcode, local_load, local_store, return_opcode,
    statements::{self, Statement, TailValue},
};

#[derive(Clone, Copy, Debug)]
pub(super) struct Binding<'a> {
    pub slot: u16,
    pub ty: &'a str,
    name: Option<&'a str>,
    suffix: usize,
}

impl Binding<'_> {
    fn names(self, name: &str) -> bool {
        if let Some(original) = self.name {
            return original == name;
        }
        let digits = name.strip_prefix("caught").unwrap_or("");
        let number = digits.trim_end_matches('_');
        number.parse::<u16>().ok() == Some(self.slot) && digits.len() - number.len() == self.suffix
    }

    pub(super) fn write(self, out: &mut String, declaration: &str) -> Result<(), KotlinError> {
        if let Some(name) = self.name {
            identifier(out, name, declaration)?;
        } else {
            write!(out, "caught{}", self.slot).expect("writing to String");
            for _ in 0..self.suffix {
                out.push('_');
            }
        }
        Ok(())
    }
}

pub(in crate::kotlin) struct TryBody<'a> {
    block: Block<'a>,
    instructions: Vec<Instruction>,
    pub lines: Vec<(u16, u16)>,
}

struct Block<'a> {
    statements: Vec<Statement<'a>>,
    end: End<'a>,
}

enum End<'a> {
    Continue,
    ReturnUnit(usize, bool),
    Return(TailValue<'a>),
    Result(TailValue<'a>),
    Throw(Binding<'a>, Range<usize>),
    Try(Box<Region<'a>>),
}

struct Region<'a> {
    start: usize,
    body: Block<'a>,
    catches: Vec<Catch<'a>>,
    finally: Option<Finally<'a>>,
    /// A store in each completing arm and a sole load/return at the exit.
    result: Option<Range<usize>>,
    next: Option<Block<'a>>,
}

struct Catch<'a> {
    binding: Binding<'a>,
    handler: usize,
    body: Block<'a>,
}

struct Finally<'a> {
    start: usize,
    statements: Vec<Statement<'a>>,
    returning: Option<TailValue<'a>>,
    copies: Vec<usize>,
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum Flow {
    /// A method exit (the last Unit return is implicit in source).
    Exit,
    /// A required exit along an arm that still has a continuation outside it.
    ExplicitExit,
    /// Falling through reaches the shared continuation, not the next handler.
    Continue,
    /// Fallthrough consumes one expression through the shared result slot.
    Result(u16),
}

#[derive(Clone, Copy)]
struct Entry<'a> {
    start: usize,
    end: usize,
    handler: usize,
    ty: Option<&'a str>,
    used: bool,
}

struct Lower<'b, 'a, 'data> {
    bytecode: &'b Bytecode<'a, 'data>,
    instructions: &'b [Instruction],
    locals: &'b Locals<'b>,
    parameters: &'b [ValueParameter],
    returns: &'b JvmType,
    declaration: &'b str,
    entries: Vec<Entry<'a>>,
    debug_locals: Vec<LocalVariable<'a>>,
}

pub(super) fn lower<'a, 'data>(
    bytecode: &Bytecode<'a, 'data>,
    instructions: Vec<Instruction>,
    start: usize,
    code: &Code<'data>,
    locals: &Locals<'_>,
    parameters: &[ValueParameter],
    returns: &JvmType,
    declaration: &str,
    trace: bool,
) -> Result<TryBody<'a>, KotlinError> {
    if code.exceptions.len() > 64 {
        return Err(invalid(declaration));
    }
    let index = |offset| {
        if usize::from(offset) == code.bytes.len() {
            return Ok(instructions.len());
        }
        at(&instructions, u32::from(offset)).ok_or_else(|| invalid(declaration))
    };
    let entries = code.exceptions.iter().map(|row| {
        let handler = index(row.handler_pc)?;
        let protected = index(row.start_pc)?;
        if protected < start || handler < start || handler == instructions.len() {
            return Err(invalid(declaration));
        }
        let ty = (row.catch_type != 0).then(|| bytecode.class.pool.class_name(row.catch_type)).transpose()?;
        Ok(Entry { start: protected, end: index(row.end_pc)?, handler, ty, used: false })
    }).collect::<Result<Vec<_>, KotlinError>>()?;
    let mut lower = Lower {
        bytecode, instructions: &instructions, locals, parameters, returns, declaration, entries,
        debug_locals: code.local_variables(&bytecode.class.pool)?,
    };
    let block = lower.block(start..instructions.len(), Flow::Exit, &mut Vec::new(), 0)?;
    if lower.entries.iter().any(|entry| !entry.used) {
        return Err(invalid(declaration));
    }
    let lines = if trace { code.line_numbers(&bytecode.class.pool)? } else { Vec::new() };
    Ok(TryBody { block, instructions, lines })
}

impl<'a> Lower<'_, 'a, '_> {
    fn block(&mut self, range: Range<usize>, flow: Flow, scope: &mut Vec<ScopedLocal<'a>>,
        depth: u8,
    ) -> Result<Block<'a>, KotlinError> {
        if depth >= 32 {
            return Err(invalid(self.declaration));
        }
        let Some(start) = self.entries.iter().filter(|entry| !entry.used && range.contains(&entry.start))
            .map(|entry| entry.start).min() else {
            return self.leaf(range, flow, scope);
        };
        if matches!(flow, Flow::Result(_)) {
            return Err(invalid(self.declaration));
        }
        let statements = self.statements(range.start..start, scope)?;
        let region = self.region(start..range.end, flow, scope, depth + 1)?;
        Ok(Block { statements, end: End::Try(Box::new(region)) })
    }

    fn statements(&self, range: Range<usize>, scope: &[ScopedLocal<'a>]) -> Result<Vec<Statement<'a>>, KotlinError> {
        statements::lower_scoped(self.bytecode, self.instructions, range, self.locals, self.declaration, scope)
    }

    fn leaf(&self, mut range: Range<usize>, flow: Flow, scope: &[ScopedLocal<'a>]) -> Result<Block<'a>, KotlinError> {
        let invalid = || invalid(self.declaration);
        let mut result = false;
        let mut terminal = End::Continue;
        let mut value_end = None;
        if let Some(last) = range.clone().next_back() {
            let instruction = &self.instructions[last];
            if instruction.opcode == return_opcode(self.returns) {
                range.end = last;
                if *self.returns == JvmType::Void {
                    terminal = End::ReturnUnit(last, flow == Flow::Exit);
                } else {
                    value_end = Some(last + 1);
                }
            } else if instruction.opcode == 0xbf {
                let load = last.checked_sub(1).filter(|load| *load >= range.start).ok_or_else(invalid)?;
                let Some((0x19, slot)) = local_load(&self.instructions[load]) else { return Err(invalid()); };
                let binding = scope.iter().rev().find_map(|local| match *local {
                    ScopedLocal::Catch(binding) if binding.slot == slot => Some(binding),
                    _ => None,
                }).ok_or_else(invalid)?;
                range.end = load;
                terminal = End::Throw(binding, load..last + 1);
            } else if let Flow::Result(slot) = flow {
                if local_store(instruction) != Some((load_opcode(self.returns) + 0x21, slot)) {
                    return Err(invalid());
                }
                range.end = last;
                value_end = Some(last + 1);
                result = true;
            }
        }
        let (statements, value) = statements::lower_open(
            self.bytecode, self.instructions, range, self.locals, self.declaration, scope,
        )?;
        match (value_end, value) {
            (Some(end), Some(mut value)) if value.expr.stack_load() == Some(load_opcode(self.returns)) => {
                value.instructions.end = end;
                terminal = if result { End::Result(value) } else { End::Return(value) };
            }
            (None, None) if !matches!(terminal, End::Continue) || flow == Flow::Continue => {}
            _ => return Err(invalid()),
        }
        Ok(Block { statements, end: terminal })
    }

    /// One contiguous protected interval with table-ordered typed handlers,
    /// optionally followed by an all-path cleanup handler. Handlers can
    /// contain nested regions when they are not themselves covered by cleanup.
    fn region(&mut self, range: Range<usize>, flow: Flow, scope: &mut Vec<ScopedLocal<'a>>,
        depth: u8,
    ) -> Result<Region<'a>, KotlinError> {
        let declaration = self.declaration;
        let invalid = || invalid(declaration);
        let mut handlers = Vec::new();
        let mut cleanup = None;
        let mut end = None;
        let mut previous = None;
        for entry in self.entries.iter_mut().filter(|entry| !entry.used && entry.start == range.start) {
            if end.is_some_and(|end| end != entry.end) || cleanup.is_some()
                || !range.contains(&entry.handler) || entry.end > entry.handler
                || previous.is_some_and(|previous| previous >= entry.handler)
                || handlers.iter().any(|old: &Entry<'_>| old.ty == entry.ty)
            {
                return Err(invalid());
            }
            end = Some(entry.end);
            previous = Some(entry.handler);
            entry.used = true;
            if entry.ty.is_some() {
                handlers.push(*entry);
            } else {
                cleanup = Some(*entry);
            }
        }
        let protected_end = end.ok_or_else(invalid)?;
        let first_handler = handlers.first().copied().or(cleanup).ok_or_else(invalid)?.handler;
        let normal_edge = first_handler - 1;
        let normal_jump = self.jump(normal_edge);
        let mut result_span = None;
        let mut result_slot = None;
        let mut normal_body = range.start..protected_end;
        let mut normal_cleanup = None;
        let returning_finally = cleanup.is_some() && handlers.is_empty()
            && *self.returns != JvmType::Void
            && normal_edge >= protected_end
            && self.instructions[normal_edge].opcode == return_opcode(self.returns)
            && self.instructions[range.end - 1].opcode == return_opcode(self.returns);
        let continuation = if normal_edge >= protected_end && let Some(join) = normal_jump {
            if join <= previous.ok_or_else(invalid)? || join >= range.end {
                return Err(invalid());
            }
            if cleanup.is_some() {
                normal_cleanup = Some(protected_end..normal_edge);
            } else if protected_end != normal_edge {
                return Err(invalid());
            }
            if matches!(flow, Flow::Exit | Flow::ExplicitExit) && *self.returns != JvmType::Void
                && let [load, ret] = &self.instructions[join..range.end]
                && ret.opcode == return_opcode(self.returns)
                && let Some((kind, slot)) = local_load(load)
                && kind == load_opcode(self.returns)
                && self.fresh(slot, scope)
            {
                result_span = Some(join..range.end);
                result_slot = Some(slot);
            }
            Some(join)
        } else if returning_finally {
            normal_cleanup = Some(protected_end..first_handler);
            None
        } else {
            if cleanup.is_some() {
                // The result load occurs AFTER cleanup, but its value is
                // produced inside the protected block. Prove that both the
                // spill and the value enter exactly this return, not a reload
                // from mutable source state in the finally copy.
                if normal_edge < protected_end || self.instructions[normal_edge].opcode != return_opcode(self.returns) {
                    return Err(invalid());
                }
                let cleanup_end = if *self.returns == JvmType::Void {
                    normal_edge
                } else {
                    let load_index = normal_edge.checked_sub(1).ok_or_else(invalid)?;
                    let Some((kind, slot)) = local_load(&self.instructions[load_index]) else { return Err(invalid()); };
                    if load_index < protected_end || kind != load_opcode(self.returns) || !self.fresh(slot, scope) {
                        return Err(invalid());
                    }
                    result_slot = Some(slot);
                    result_span = Some(load_index..normal_edge + 1);
                    load_index
                };
                normal_cleanup = Some(protected_end..cleanup_end);
            } else if protected_end == first_handler {
                // Direct normal return is part of the protected interval.
            } else if protected_end == normal_edge && self.instructions[normal_edge].opcode == return_opcode(self.returns) {
                normal_body.end = first_handler;
            } else {
                return Err(invalid());
            }
            None
        };
        let handler_limit = continuation.unwrap_or(range.end);
        let mut finally = if let Some(entry) = cleanup {
            let normal = normal_cleanup.as_ref().ok_or_else(invalid)?;
            Some(self.finally(entry, handler_limit, normal.clone(), result_slot, returning_finally, scope)?)
        } else {
            None
        };
        let inner_flow = if let Some(slot) = result_slot {
            Flow::Result(slot)
        } else if continuation.is_some() || finally.is_some() {
            // The branch or return beyond cleanup is lowered separately.
            Flow::Continue
        } else if flow == Flow::Exit {
            Flow::Exit
        } else {
            Flow::ExplicitExit
        };
        if let Some(slot) = result_slot {
            let store = protected_end.checked_sub(1).filter(|&i| i >= range.start).ok_or_else(invalid)?;
            if local_store(&self.instructions[store]) != Some((load_opcode(self.returns) + 0x21, slot)) {
                return Err(invalid());
            }
        }
        if self.has_pending(&normal_body) {
            // Overlapping protected regions require proving dispatch priority
            // between the inner table and all enclosing handlers.
            return Err(invalid());
        }
        let body = self.leaf(normal_body, inner_flow, scope)?;
        let mut catches = Vec::with_capacity(handlers.len());
        for (index, entry) in handlers.iter().enumerate() {
            let limit = handlers.get(index + 1).map(|entry| entry.handler)
                .or_else(|| cleanup.map(|entry| entry.handler)).unwrap_or(handler_limit);
            let start = entry.handler + 1;
            if start > limit {
                return Err(invalid());
            }
            let mut end = limit;
            if let (Some(cleanup), Some(finally), Some(normal)) = (cleanup, &mut finally, &normal_cleanup) {
                end = self.cleanup_interval(entry.handler, cleanup.handler, limit)?.ok_or_else(invalid)?;
                let Some(join) = continuation else { return Err(invalid()); };
                let bridge = limit - 1;
                if end < start || end > bridge || self.jump(bridge) != Some(join) || !self.same_code(normal.clone(), end..bridge) {
                    return Err(invalid());
                }
                finally.copies.push(end);
                if self.has_pending(&(start..end)) {
                    return Err(invalid());
                }
            } else if let Some(join) = continuation {
                if start < limit && self.jump(limit - 1) == Some(join) {
                    end -= 1;
                } else if limit != join && !self.terminates(start..limit) {
                    // No physical fallthrough from one handler into another.
                    return Err(invalid());
                }
            }
            let Some((0x3a, slot)) = local_store(&self.instructions[entry.handler]) else { return Err(invalid()); };
            if !self.fresh(slot, scope) || result_slot == Some(slot) {
                return Err(invalid());
            }
            let ty = entry.ty.expect("typed handlers only");
            if ty.starts_with('[') || ty.contains('$') {
                return Err(invalid());
            }
            let binding = self.binding(slot, ty, start..end, scope);
            scope.push(ScopedLocal::Catch(binding));
            let arm = self.block(start..end, inner_flow, scope, depth)?;
            let _ = scope.pop();
            catches.push(Catch { handler: entry.handler, binding, body: arm });
        }
        let next = match (continuation, &result_span) {
            (Some(join), None) => Some(self.block(join..range.end, flow, scope, depth)?),
            (None, None) if finally.is_some() && !returning_finally => Some(Block {
                statements: Vec::new(),
                end: End::ReturnUnit(normal_edge, flow == Flow::Exit),
            }),
            _ => None,
        };
        Ok(Region { start: range.start, body, catches, finally, result: result_span, next })
    }

    fn has_pending(&self, range: &Range<usize>) -> bool {
        self.entries.iter().any(|entry| !entry.used && range.contains(&entry.start))
    }

    fn binding(&self, slot: u16, ty: &'a str, range: Range<usize>, scope: &[ScopedLocal<'a>]) -> Binding<'a> {
        let conflicts = |candidate: &str| {
            self.parameters.iter().any(|parameter| parameter.name == candidate)
                || scope.iter().any(|local| matches!(*local, ScopedLocal::Catch(binding) if binding.names(candidate)))
        };
        let start = self.offset(range.start);
        let end = self.offset(range.end);
        let name = self.debug_locals.iter().find(|local| {
            local.index == slot && u32::from(local.start_pc) == start
                && u32::from(local.length) == end - start
                && local.descriptor.strip_prefix('L').and_then(|s| s.strip_suffix(';')) == Some(ty)
                && !conflicts(local.name)
        }).map(|local| local.name);
        let mut suffix = 0;
        if name.is_none() {
            let mut generated = format!("caught{slot}");
            while conflicts(&generated) {
                generated.push('_');
                suffix += 1;
            }
        }
        Binding { slot, ty, name, suffix }
    }

    fn finally(&mut self, entry: Entry<'a>, limit: usize, normal: Range<usize>, result: Option<u16>,
        returning: bool, scope: &[ScopedLocal<'a>],
    ) -> Result<Finally<'a>, KotlinError> {
        let declaration = self.declaration;
        let invalid = || invalid(declaration);
        let handler = entry.handler;
        if limit - handler < 3 {
            return Err(invalid());
        }
        let Some((0x3a, slot)) = local_store(&self.instructions[handler]) else { return Err(invalid()); };
        let copy = handler + 1..if returning { limit } else { limit - 2 };
        if !self.fresh(slot, scope) || Some(slot) == result
            || (!returning && (local_load(&self.instructions[limit - 2]) != Some((0x19, slot))
                || self.instructions[limit - 1].opcode != 0xbf))
            || !self.same_code(normal.clone(), copy.clone())
            || result.is_some_and(|result| self.writes_slot(normal.clone(), result, self.returns.slots()))
            || self.writes_slot(copy.clone(), slot, 1)
        {
            return Err(invalid());
        }
        // Kotlin can cover the exception spill itself with a self edge. The
        // spill cannot throw and no executable cleanup belongs in this row.
        if self.cleanup_interval(handler, handler, limit)?.is_some_and(|end| end != copy.start) {
            return Err(invalid());
        }
        let (statements, returning) = if returning {
            // Both copies return outright: there is no continuation and no
            // saved result to reload after cleanup.
            let Block { statements, end: End::Return(value) } = self.leaf(normal.clone(), Flow::Exit, scope)? else {
                return Err(invalid());
            };
            (statements, Some(value))
        } else {
            (self.statements(normal.clone(), scope)?, None)
        };
        Ok(Finally { start: normal.start, statements, returning, copies: vec![copy.start] })
    }

    fn cleanup_interval(&mut self, start: usize, target: usize, limit: usize) -> Result<Option<usize>, KotlinError> {
        let mut end = None;
        for entry in self.entries.iter_mut().filter(|entry| !entry.used && entry.start == start
            && entry.handler == target && entry.ty.is_none())
        {
            if entry.end > limit || end.is_some() {
                return Err(invalid(self.declaration));
            }
            entry.used = true;
            end = Some(entry.end);
        }
        Ok(end)
    }

    fn fresh(&self, slot: u16, scope: &[ScopedLocal<'a>]) -> bool {
        slot >= self.locals.next_slot() && !scope.iter().any(|local| local.slot() == slot)
    }

    fn writes_slot(&self, range: Range<usize>, slot: u16, width: u16) -> bool {
        let overlaps = |other: u16, other_width| {
            other < slot.saturating_add(width) && slot < other.saturating_add(other_width)
        };
        self.instructions[range].iter().any(|instruction| {
            local_store(instruction).is_some_and(|(op, other)| overlaps(other, if matches!(op, 0x37 | 0x39) { 2 } else { 1 }))
                || matches!(instruction.operand, Operand::Increment { index, .. } if overlaps(index, 1))
        })
    }

    fn same_code(&self, a: Range<usize>, b: Range<usize>) -> bool {
        a.len() == b.len() && self.instructions[a].iter().zip(&self.instructions[b]).all(|(a, b)| {
            a.opcode == b.opcode && a.operand == b.operand
        })
    }

    fn terminates(&self, range: Range<usize>) -> bool {
        self.instructions[range].last().is_some_and(|instruction| matches!(instruction.opcode, 0xac..=0xb1 | 0xbf))
    }

    fn jump(&self, index: usize) -> Option<usize> {
        let instruction = &self.instructions[index];
        match (instruction.opcode, &instruction.operand) {
            (0xa7 | 0xc8, Operand::Branch(target)) if *target > instruction.offset => at(self.instructions, *target),
            _ => None,
        }
    }

    fn offset(&self, index: usize) -> u32 {
        self.instructions.get(index).map_or_else(|| {
            let last = self.instructions.last().expect("nonempty protected bytecode");
            last.offset + last.len
        }, |instruction| instruction.offset)
    }
}

fn at(instructions: &[Instruction], offset: u32) -> Option<usize> {
    instructions.binary_search_by_key(&offset, |instruction| instruction.offset).ok()
}

fn invalid(declaration: &str) -> KotlinError {
    KotlinError::unsupported(declaration, "unsupported Kotlin exception region")
}
