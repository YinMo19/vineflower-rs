// Based on Vineflower's IdeaNotNullPass (Apache-2.0).
use std::collections::BTreeSet;

use crate::{
    bytecode::{Instruction, Operand, decode},
    classfile::{Annotation, ClassError, ClassFile, Code, Constant, Member},
    descriptor::MethodDescriptor,
};

const NOT_NULL: &str = "Lorg/jetbrains/annotations/NotNull;";
const REPORT: &str = "$$$reportNull$$$0";

/// Remove compiler-generated guards from annotated parameters and returns.
/// Replace instructions by no-ops to keep branch, LVT and debug offsets stable.
pub(crate) fn strip_guards(
    class: &ClassFile<'_>,
    method: &Member<'_>,
    code: &Code<'_>,
    descriptor: &MethodDescriptor,
    instructions: &mut [Instruction],
) -> Result<(), ClassError> {
    let pool = &class.pool;
    let has_not_null = |annotations: &[Annotation]| -> Result<bool, ClassError> {
        for annotation in annotations {
            if pool.utf8(annotation.type_index)? == NOT_NULL {
                return Ok(true);
            }
        }
        Ok(false)
    };
    let checked_returns = has_not_null(&method.annotations(pool, false)?)?;
    let parameter_annotations = method.parameter_annotations(pool, false)?;
    let mut checked_slots = BTreeSet::new();
    let skip = descriptor
        .parameters
        .len()
        .saturating_sub(parameter_annotations.len());
    let mut slot = u16::from(method.access_flags & 0x0008 == 0);
    for (index, param) in descriptor.parameters.iter().enumerate() {
        if let Some(i) = index.checked_sub(skip)
            && let Some(group) = parameter_annotations.get(i)
            && has_not_null(group)?
        {
            checked_slots.insert(slot);
        }
        slot += param.slots();
    }
    if !checked_returns && checked_slots.is_empty() {
        return Ok(());
    }
    if !has_reporter(class)? {
        return Ok(());
    }
    let owner = pool.class_name(class.this_class)?;
    let is_report = |instruction: &Instruction| -> Result<bool, ClassError> {
        let (0xb8, Operand::Constant(idx)) = (instruction.opcode, &instruction.operand) else {
            return Ok(false);
        };
        Ok(pool.member_ref(*idx)? == (owner, REPORT, "(I)V"))
    };
    let is_reason = |instruction: &Instruction| -> Result<bool, ClassError> {
        Ok(match (instruction.opcode, &instruction.operand) {
            (0x03..=0x08 | 0x10..=0x11, _) => true,
            (0x12 | 0x13, Operand::Constant(idx)) => {
                matches!(pool.get(*idx)?, Constant::Integer(_))
            }
            _ => false,
        })
    };
    let mut targets = BTreeSet::new();
    for instruction in &*instructions {
        match &instruction.operand {
            Operand::Branch(target) => {
                targets.insert(*target);
            }
            Operand::Switch { default, cases } => {
                targets.insert(*default);
                targets.extend(cases.iter().map(|&(_, offset)| offset));
            }
            _ => {}
        }
    }
    for exception in &code.exceptions {
        targets.extend([exception.start_pc, exception.end_pc, exception.handler_pc].map(u32::from));
    }
    let has_entry = |instructions: &[Instruction]| {
        instructions
            .iter()
            .any(|instruction| targets.contains(&instruction.offset))
    };

    let mut checked_prefix = 0;
    while let Some([load, test, reason, call, resume]) =
        instructions.get(checked_prefix..checked_prefix + 5)
    {
        let slot = match (load.opcode, &load.operand) {
            (0x19, Operand::Local(index)) => *index,
            (0x2a..=0x2d, _) => u16::from(load.opcode - 0x2a),
            _ => break,
        };
        if !checked_slots.contains(&slot)
            || !nonnull_to(test, resume)
            || !is_reason(reason)?
            || !is_report(call)?
            || has_entry(&instructions[checked_prefix + 1..checked_prefix + 4])
        {
            break;
        }
        // Only strip entry guards, not hand-written checks encountered later.
        // Subsequent leading guards naturally have incoming edges from the
        // preceding guard, which is itself removed by this pass.
        make_nops(&mut instructions[checked_prefix..checked_prefix + 4]);
        checked_prefix += 4;
    }
    if checked_returns {
        let mut index = checked_prefix;
        while let Some([dup, test, reason, call, ret]) = instructions.get(index..index + 5) {
            if dup.opcode == 0x59
                && ret.opcode == 0xb0
                && nonnull_to(test, ret)
                && is_reason(reason)?
                && is_report(call)?
                && !has_entry(&instructions[index + 1..index + 4])
            {
                make_nops(&mut instructions[index..index + 4]);
                index += 5;
            } else {
                index += 1;
            }
        }
    }
    Ok(())
}

fn nonnull_to(test: &Instruction, resume: &Instruction) -> bool {
    test.opcode == 0xc7 && test.operand == Operand::Branch(resume.offset)
}

fn make_nops(instructions: &mut [Instruction]) {
    for instruction in instructions {
        instruction.opcode = 0;
        instruction.operand = Operand::None;
    }
}

fn has_reporter(class: &ClassFile<'_>) -> Result<bool, ClassError> {
    let pool = &class.pool;
    for helper in &class.methods {
        if helper.access_flags & 0x100a == 0x100a
            && pool.utf8(helper.name_index)? == REPORT
            && pool.utf8(helper.descriptor_index)? == "(I)V"
            && let Some(code) = helper.code(pool)?
            && let Ok(instructions) = decode(code.bytes)
        {
            return Ok(instructions.iter().any(|op| op.opcode == 0xbf)
                && instructions
                    .iter()
                    .all(|op| !matches!(op.opcode, 0xac..=0xb1 | 0xb3 | 0xb5 | 0xba)));
        }
    }
    Ok(false)
}
