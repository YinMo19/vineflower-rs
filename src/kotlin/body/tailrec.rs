// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.

use super::{
    Body, Bytecode, Code, Expr, Instruction, KotlinError, Locals,
    MethodDescriptor, Operand, StackValue, ValueParameter, control, invocations, load_opcode,
    local_load, local_store, return_opcode,
};

pub(super) fn has_back_edge(instructions: &[Instruction]) -> bool {
    instructions.iter().any(|instruction| {
        matches!(instruction.operand, Operand::Branch(target) if target <= instruction.offset)
    })
}

pub(super) fn lower<'a, 'data>(
    bytecode: &Bytecode<'a, 'data>,
    instructions: &mut [Instruction],
    descriptor: &MethodDescriptor,
    code: &Code<'data>,
    locals: &mut Locals<'_>,
    parameters: &[ValueParameter],
    declaration: &str,
    trace: bool,
) -> Result<Body<'a>, KotlinError> {
    let invalid = || invalid(declaration);
    if locals.has_extension_receiver() {
        return Err(invalid());
    }
    // Kotlin stages the instance receiver too. It may only be committed
    // from the original `this`, so regular calls through the alias can be
    // rendered exactly like calls through the JVM dispatch receiver.
    let mut first_scratch = locals.next_slot();
    let aliases_this = locals.instance && matches!(&*instructions, [load, store, ..]
        if local_load(load) == Some((0x19, 0)) && local_store(store) == Some((0x3a, first_scratch)));
    let instructions = if aliases_this {
        locals.dispatch_alias = Some(first_scratch);
        first_scratch = first_scratch.checked_add(1).ok_or_else(invalid)?;
        &mut instructions[2..]
    } else {
        instructions
    };
    if first_scratch > code.max_locals {
        return Err(invalid());
    }
    let header = instructions.first().ok_or_else(invalid)?.offset;
    let ret = return_opcode(&descriptor.return_type);
    for instruction in instructions.iter_mut() {
        if let Operand::Branch(target) = instruction.operand
            && target <= instruction.offset
        {
            if !matches!(instruction.opcode, 0xa7 | 0xc8) || target != header {
                return Err(invalid());
            }
            // To structure the forward graph, each back edge is a terminal.
            // Its original branch operand marks it for the staged-call proof.
            instruction.opcode = ret;
        }
    }
    let shape = Shape { first_scratch, max_locals: code.max_locals };
    let (expr, materialized) = control::lower(
        bytecode, instructions, locals, &descriptor.return_type, parameters, declaration, Some(shape),
    )?;
    bytecode.return_expression(expr, instructions, code, trace, materialized)
}

#[derive(Clone, Copy)]
pub(super) struct Shape {
    first_scratch: u16,
    max_locals: u16,
}

impl Shape {
    pub(super) fn call<'a>(
        self,
        bytecode: &Bytecode<'a, '_>,
        instructions: &[Instruction],
        locals: &Locals<'_>,
        arguments: &mut Vec<StackValue<'a>>,
        declaration: &str,
    ) -> Result<Expr<'a>, KotlinError> {
        let invalid = || invalid(declaration);
        let destinations = locals.dispatch_alias.into_iter().map(|slot| (slot, 0x19, 1))
            .chain(locals.slots.iter().map(|&(slot, ty)| (slot, load_opcode(ty), ty.slots())));
        let commits = 2 * (locals.slots.len() + usize::from(locals.dispatch_alias.is_some()));
        if commits == 0 {
            return Err(invalid());
        }
        let commit_start = instructions.len().checked_sub(commits).ok_or_else(invalid)?;
        let (mut staging, commits) = instructions.split_at(commit_start);
        let mut first_free = self.first_scratch;
        let mut operand = Vec::new();
        for ((slot, load, width), pair) in destinations.zip(commits.chunks_exact(2)) {
            let (_, scratch) = local_load(&pair[0]).filter(|&(op, _)| op == load).ok_or_else(invalid)?;
            let store = load + 0x21;
            if scratch < first_free || local_store(&pair[1]) != Some((store, slot)) {
                return Err(invalid());
            }
            first_free = scratch.checked_add(width).filter(|&end| end <= self.max_locals).ok_or_else(invalid)?;
            // Values must be staged in source argument order, before *any*
            // parameter changes. No argument may read out of a scratch slot
            // or consume a value left on the operand stack by its predecessor.
            let spill = loop {
                let (instruction, rest) = staging.split_first().ok_or_else(invalid)?;
                staging = rest;
                if let Some(spill) = local_store(instruction) {
                    break spill;
                }
                bytecode.expression(instruction, locals, &mut operand, declaration)?;
            };
            if spill != (store, scratch) || operand.len() != 1 {
                return Err(invalid());
            }
            let value = operand.pop().unwrap();
            if locals.dispatch_alias == Some(slot) {
                if !matches!(value, StackValue::This) {
                    return Err(invalid());
                }
            } else if matches!(&value, StackValue::Value(expr) if expr.stack_load() == Some(load)) {
                arguments.push(value);
            } else {
                return Err(invalid());
            }
        }
        if !staging.is_empty() {
            return Err(invalid());
        }
        invocations::tail_call(bytecode, locals, arguments, declaration)
    }
}

fn invalid(declaration: &str) -> KotlinError {
    KotlinError::unsupported(declaration, "unproven Kotlin tail-recursive parameter updates")
}
