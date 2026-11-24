// Based on Vineflower's qualified creation and constructor-expression passes (Apache-2.0).
// Copyright 2000-2021 JetBrains s.r.o.
use std::collections::BTreeSet;

use crate::{
    bytecode::{Instruction, Operand},
    classfile::{ClassError, ClassFile, Constant, ConstantPool, ExceptionHandler, Member},
    context::ClassGroup,
    descriptor::{MethodDescriptor, Type},
    legacy::straight_line_stack_effect,
};

/// javac emits a null-check solely for the Java source syntax `outer.new` or
/// `outer.super`. Discard its duplicate, call and pop before lifting, when
/// the guarded value provably remains the first enclosing-instance argument.
/// The retained qualified expression performs the check at the same point.
/// Offsets and widths are unchanged for debug ranges, handlers and CFG input.
pub(crate) fn mask_guards(
    class: &ClassFile<'_>,
    method: &Member<'_>,
    group: &ClassGroup<'_>,
    instructions: &mut [Instruction],
    handlers: &[ExceptionHandler],
) -> Result<(), ClassError> {
    let pool = &class.pool;
    let mut leaders = None;
    for start in 0..instructions.len().saturating_sub(2) {
        let [dup, check, pop] = &instructions[start..start + 3] else { unreachable!() };
        if dup.opcode != 0x59 || pop.opcode != 0x57 || !compiler_null_check(check, pool)? {
            continue;
        }
        let leaders = leaders.get_or_insert_with(|| entry_boundaries(instructions, handlers));
        let superclass = (pool.utf8(method.name_index)? == "<init>" && class.super_class != 0)
            .then(|| pool.class_name(class.super_class))
            .transpose()?;
        let Some(call) = guarded_constructor(group, pool, instructions, leaders, start + 3)? else { continue };
        let qualified_new = allocation_start(pool, instructions, leaders, start, call.owner)?;
        let qualified_super = !qualified_new && superclass == Some(call.owner)
            && super_receiver_start(pool, instructions, leaders, start, pool.class_name(class.this_class)?, call.owner)?;
        if qualified_new || qualified_super {
            for op in &mut instructions[start..start + 3] {
                op.opcode = 0x00;
                op.operand = Operand::None;
            }
        }
    }
    Ok(())
}

fn entry_boundaries(ops: &[Instruction], handlers: &[ExceptionHandler]) -> BTreeSet<u32> {
    let mut leaders = BTreeSet::new();
    for op in ops {
        match &op.operand {
            Operand::Branch(target) => { leaders.insert(*target); }
            Operand::Switch { default, cases } => {
                leaders.insert(*default);
                leaders.extend(cases.iter().map(|(_, target)| *target));
            }
            _ => {}
        }
    }
    for handler in handlers {
        leaders.extend([handler.start_pc, handler.end_pc, handler.handler_pc].map(u32::from));
    }
    leaders
}

fn compiler_null_check(op: &Instruction, pool: &ConstantPool<'_>) -> Result<bool, ClassError> {
    let (0xb6 | 0xb8, Operand::Constant(index)) = (op.opcode, &op.operand) else {
        return Ok(false);
    };
    if !matches!(pool.get(*index)?, Constant::Methodref { .. }) {
        return Ok(false);
    }
    let member = pool.member_ref(*index)?;
    Ok((op.opcode, member) == (0xb6, ("java/lang/Object", "getClass", "()Ljava/lang/Class;"))
        || (op.opcode, member) == (0xb8, ("java/util/Objects", "requireNonNull", "(Ljava/lang/Object;)Ljava/lang/Object;")))
}

struct Constructor<'a> {
    owner: &'a str,
    descriptor: &'a str,
}

fn constructor_call<'a>(
    op: &Instruction,
    pool: &'a ConstantPool<'_>,
) -> Result<Option<Constructor<'a>>, ClassError> {
    let (0xb7, Operand::Constant(index)) = (op.opcode, &op.operand) else {
        return Ok(None);
    };
    if !matches!(pool.get(*index)?, Constant::Methodref { .. }) {
        return Ok(None);
    }
    let (owner, name, descriptor) = pool.member_ref(*index)?;
    Ok((name == "<init>").then_some(Constructor { owner, descriptor }))
}

fn guarded_constructor<'a>(
    group: &ClassGroup<'_>,
    pool: &'a ConstantPool<'_>,
    ops: &[Instruction],
    entries: &BTreeSet<u32>,
    at: usize,
) -> Result<Option<Constructor<'a>>, ClassError> {
    if ops[at - 2..at].iter().any(|op| entries.contains(&op.offset)) {
        return Ok(None);
    }
    let mut available = 0u16;
    for op in &ops[at..] {
        if entries.contains(&op.offset) {
            return Ok(None);
        }
        if let Some(call) = constructor_call(op, pool)?
            && group.constructor_outer(call.owner, call.descriptor).is_some()
            && let Ok(descriptor) = MethodDescriptor::parse(call.descriptor)
            && descriptor.return_type == Type::Void
            && descriptor.parameters.iter().map(Type::slots).sum::<u16>().checked_sub(1) == Some(available)
        {
            return Ok(Some(call));
        }
        let Some(next) = step(available, op, pool) else { return Ok(None) };
        available = next;
    }
    Ok(None)
}

fn allocation_start(
    pool: &ConstantPool<'_>,
    ops: &[Instruction],
    entries: &BTreeSet<u32>,
    guard: usize,
    owner: &str,
) -> Result<bool, ClassError> {
    if entries.contains(&ops[guard].offset) {
        return Ok(false);
    }
    // Walk back from the qualifier expression. The required depth is the
    // unique incoming slot height if every operation stays above the pending
    // allocation. The running minimum catches stack permutations and pops.
    let mut suffix = Suffix::default();
    for index in (0..guard).rev() {
        let op = &ops[index];
        if op.opcode == 0x59 && index > 0 && !entries.contains(&op.offset)
            && let (0xbb, Operand::Constant(class)) = (ops[index - 1].opcode, &ops[index - 1].operand)
            && pool.class_name(*class)? == owner
            && suffix.required == 0 && suffix.minimum == 0
        {
            return Ok(true);
        }
        if entries.contains(&op.offset) || !suffix.prepend(op, pool) {
            return Ok(false);
        }
    }
    Ok(false)
}

fn super_receiver_start(
    pool: &ConstantPool<'_>,
    ops: &[Instruction],
    entries: &BTreeSet<u32>,
    guard: usize,
    owner: &str,
    superclass: &str,
) -> Result<bool, ClassError> {
    if entries.contains(&ops[guard].offset) {
        return Ok(false);
    }
    let mut suffix = Suffix::default();
    for index in (0..guard).rev() {
        let op = &ops[index];
        if matches!((op.opcode, &op.operand), (0x2a, _) | (0x19, Operand::Local(0)))
            && suffix.required == 0 && suffix.minimum == 0
        {
            for previous in &ops[..index] {
                if let Some(call) = constructor_call(previous, pool)?
                    && (call.owner == owner || call.owner == superclass)
                {
                    return Ok(false);
                }
            }
            return Ok(true);
        }
        if entries.contains(&op.offset) || !suffix.prepend(op, pool) {
            return Ok(false);
        }
    }
    Ok(false)
}

fn step(available: u16, op: &Instruction, pool: &ConstantPool<'_>) -> Option<u16> {
    let (pop, push) = straight_line_stack_effect(op, pool)?;
    available.checked_sub(pop)?.checked_add(push)
}

/// Tracks the incoming depth needed to leave one qualifier slot and the
/// minimum incoming depth to execute its operations. No path may consume an
/// earlier value, including an uninitialized receiver outside the expression.
struct Suffix {
    required: i32,
    minimum: i32,
}

impl Default for Suffix {
    fn default() -> Self {
        Self { required: 1, minimum: 0 }
    }
}

impl Suffix {
    fn prepend(&mut self, op: &Instruction, pool: &ConstantPool<'_>) -> bool {
        let Some((pop, push)) = straight_line_stack_effect(op, pool) else { return false };
        let pop = i32::from(pop);
        let push = i32::from(push);
        self.required += pop - push;
        self.minimum = (self.minimum + pop - push).max(pop);
        true
    }
}
