// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.

use super::{
    Bytecode, Expr, ExprKind, Instruction, JvmFieldSignature, JvmMethodSignature, JvmType,
    KotlinError, Locals, MethodDescriptor, Operand, Primitive, STATIC, ValueParameter, load_opcode,
    local_load, local_store, pop_value, return_opcode,
};

/// Recover Kotlin's ordered default-mask clauses. Expressions must be pure,
/// evaluate to a single value, and refer only to earlier parameters.
pub(in crate::kotlin) fn recover<'a>(
    bytecode: &Bytecode<'a, '_>,
    signature: &JvmMethodSignature,
    parameters: &[ValueParameter],
    instance: bool,
    declaration: &str,
) -> Result<Vec<(usize, Expr<'a>)>, KotlinError> {
    let defaults = parameters
        .iter()
        .filter(|parameter| parameter.flags.has(1))
        .count();
    if defaults == 0 {
        return Ok(Vec::new());
    }
    let mut output = Vec::with_capacity(defaults);
    let mut stack = Vec::new();
    dispatch(
        bytecode,
        signature,
        parameters,
        instance,
        declaration,
        |index, _, locals, expression| {
            for instruction in expression {
                bytecode.expression(instruction, locals, &mut stack, declaration)?;
            }
            if stack.len() != 1 {
                return Err(invalid(declaration));
            }
            let value = pop_value(&mut stack, declaration)?;
            if !value.references_only_earlier_parameters(index) {
                return Err(invalid(declaration));
            }
            output.push((index, value));
            Ok(())
        },
    )?;
    Ok(output)
}

pub(in crate::kotlin) fn verify_copy_defaults(
    bytecode: &Bytecode<'_, '_>,
    signature: &JvmMethodSignature,
    parameters: &[ValueParameter],
    fields: &[(&JvmFieldSignature, &str)],
) -> Result<(), KotlinError> {
    dispatch(
        bytecode,
        signature,
        parameters,
        true,
        &signature.name,
        |index, _, _, expression| {
            let &(field, descriptor) = fields.get(index).ok_or_else(|| invalid(&signature.name))?;
            if matches!(expression, [receiver, get] if local_load(receiver) == Some((0x19, 0))
            && bytecode.reference(get, 0xb4)? == Some((bytecode.owner, field.name.as_str(), descriptor)))
            {
                Ok(())
            } else {
                Err(invalid(&signature.name))
            }
        },
    )
}

fn dispatch(
    bytecode: &Bytecode<'_, '_>,
    signature: &JvmMethodSignature,
    parameters: &[ValueParameter],
    instance: bool,
    declaration: &str,
    mut default: impl FnMut(
        usize,
        &ValueParameter,
        &Locals<'_>,
        &[Instruction],
    ) -> Result<(), KotlinError>,
) -> Result<(), KotlinError> {
    let invalid = || invalid(declaration);
    let constructor = signature.name == "<init>";
    let locals = Locals::new(&signature.descriptor, instance, parameters, declaration)?;
    let masks = parameters.len().div_ceil(32);
    let mut helper_parameters =
        Vec::with_capacity(parameters.len() + masks + 1 + usize::from(instance && !constructor));
    if instance && !constructor {
        helper_parameters.push(JvmType::Object(bytecode.owner.to_owned()));
    }
    helper_parameters.extend_from_slice(&signature.descriptor.parameters);
    helper_parameters.resize(
        helper_parameters.len() + masks,
        JvmType::Primitive(Primitive::Int),
    );
    helper_parameters.push(JvmType::Object(
        if constructor {
            "kotlin/jvm/internal/DefaultConstructorMarker"
        } else {
            "java/lang/Object"
        }
        .to_owned(),
    ));
    let helper = JvmMethodSignature {
        name: if constructor {
            "<init>".to_owned()
        } else {
            format!("{}$default", signature.name)
        },
        descriptor: MethodDescriptor {
            parameters: helper_parameters,
            return_type: signature.descriptor.return_type.clone(),
        },
    };
    let member = bytecode
        .find_method(&helper)?
        .filter(|method| {
            method.access_flags & 0x1000 != 0 && (method.access_flags & STATIC != 0) != constructor
        })
        .ok_or_else(invalid)?;
    let instructions = bytecode.instructions(member, declaration)?;
    let first_mask = u16::from(instance)
        + signature
            .descriptor
            .parameters
            .iter()
            .map(JvmType::slots)
            .sum::<u16>();
    let mut cursor = 0;
    let mut mask_value = Vec::new();
    for (index, parameter) in parameters
        .iter()
        .enumerate()
        .filter(|(_, p)| p.flags.has(1))
    {
        if parameter.vararg_element.is_some() {
            return Err(invalid());
        }
        let [load, mask, and, jump, ..] = &instructions[cursor..] else {
            return Err(invalid());
        };
        let Operand::Branch(target) = jump.operand else {
            return Err(invalid());
        };
        if local_load(load) != Some((0x15, first_mask + (index / 32) as u16))
            || and.opcode != 0x7e
            || jump.opcode != 0x99
        {
            return Err(invalid());
        }
        bytecode.expression(mask, &locals, &mut mask_value, declaration)?;
        if !matches!(pop_value(&mut mask_value, declaration)?.kind, ExprKind::Literal(super::Literal::Int(value))
            if value == (1u32 << (index % 32)) as i32)
        {
            return Err(invalid());
        }
        let start = cursor + 4;
        cursor = instructions
            .binary_search_by_key(&target, |instruction| instruction.offset)
            .map_err(|_| invalid())?;
        if cursor <= start {
            return Err(invalid());
        }
        let (store, expression) = instructions[start..cursor].split_last().unwrap();
        let (slot, ty) = locals.slots[index];
        if local_store(store) != Some((load_opcode(ty) + 0x21, slot)) {
            return Err(invalid());
        }
        default(index, parameter, &locals, expression)?;
    }
    let tail = &instructions[cursor..];
    let [loads @ .., call, ret] = tail else {
        return Err(invalid());
    };
    let loads = if instance {
        let Some((receiver, rest)) = loads.split_first() else {
            return Err(invalid());
        };
        if local_load(receiver) != Some((0x19, 0)) {
            return Err(invalid());
        }
        rest
    } else {
        loads
    };
    if loads.len() != locals.slots.len()
        || loads
            .iter()
            .zip(&locals.slots)
            .any(|(load, &(slot, ty))| local_load(load) != Some((load_opcode(ty), slot)))
    {
        return Err(invalid());
    }
    let invoke = if constructor {
        0xb7
    } else if instance {
        0xb6
    } else {
        0xb8
    };
    let method = bytecode
        .reference(call, invoke)?
        .or(if instance && !constructor {
            bytecode.reference(call, 0xb7)?
        } else {
            None
        });
    let (owner, name, descriptor) = method.ok_or_else(invalid)?;
    if owner != bytecode.owner
        || name != signature.name
        || MethodDescriptor::parse(descriptor)? != signature.descriptor
        || ret.opcode != return_opcode(&signature.descriptor.return_type)
    {
        return Err(invalid());
    }
    Ok(())
}

pub(in crate::kotlin) fn verify_copy(
    bytecode: &Bytecode<'_, '_>,
    signature: &JvmMethodSignature,
    parameters: &[ValueParameter],
) -> Result<(), KotlinError> {
    let invalid =
        || KotlinError::unsupported(&signature.name, "nontrivial data class copy implementation");
    let member = bytecode
        .find_method(signature)?
        .filter(|member| member.access_flags & STATIC == 0)
        .ok_or_else(invalid)?;
    let locals = Locals::new(&signature.descriptor, true, parameters, &signature.name)?;
    let instructions = bytecode.instructions(member, &signature.name)?;
    let instructions = bytecode.parameter_checks(&instructions, &locals, parameters)?;
    let [new, dup, loads @ .., call, ret] = instructions else {
        return Err(invalid());
    };
    let Operand::Constant(class) = new.operand else {
        return Err(invalid());
    };
    if new.opcode != 0xbb
        || bytecode.class.pool.class_name(class)? != bytecode.owner
        || dup.opcode != 0x59
        || ret.opcode != 0xb0
        || loads.len() != locals.slots.len()
        || loads
            .iter()
            .zip(&locals.slots)
            .any(|(load, &(slot, ty))| local_load(load) != Some((load_opcode(ty), slot)))
    {
        return Err(invalid());
    }
    let (owner, name, descriptor) = bytecode.reference(call, 0xb7)?.ok_or_else(invalid)?;
    let descriptor = MethodDescriptor::parse(descriptor)?;
    if owner != bytecode.owner
        || name != "<init>"
        || descriptor.return_type != JvmType::Void
        || descriptor.parameters != signature.descriptor.parameters
    {
        return Err(invalid());
    }
    Ok(())
}

fn invalid(declaration: &str) -> KotlinError {
    KotlinError::unsupported(declaration, "unrecognized JVM default argument dispatcher")
}
