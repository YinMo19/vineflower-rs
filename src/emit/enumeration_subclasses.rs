// Based on Vineflower's enum and anonymous class recovery (Apache-2.0).

use crate::{
    ClassGroup,
    bytecode::{Instruction, Operand, decode},
    classfile::{ClassFile, Code, Member},
    context::NestedKind,
    descriptor::{MethodDescriptor, Primitive, Type},
    lift::AnonymousSite,
};

use super::{
    CONSTRUCTOR_PREFIX, DecompileError, ENUM, FINAL, PRIVATE, STATIC, SYNTHETIC, local, member,
    parse, unsupported,
};

pub(super) struct ConstantSubclass<'a> {
    pub site: AnonymousSite,
    pub bridge: Option<&'a str>,
}

pub(super) fn recover<'a>(
    group: &'a ClassGroup<'_>,
    parent: &'a ClassFile<'_>,
    owner: &str,
    allocated: &str,
    descriptor: &str,
    ty: &MethodDescriptor,
) -> Result<ConstantSubclass<'a>, DecompileError> {
    let fail = || unsupported("unverified enum constant subclass");
    let node = group.nested_class(allocated).ok_or_else(fail)?;
    let subclass = group.get(allocated).ok_or_else(fail)?;
    let pool = &subclass.pool;
    if !group.is_attached(allocated)
        || !matches!(node.kind, NestedKind::Anonymous)
        || node.outer != owner
        || node.method.is_some()
        || !subclass.interfaces.is_empty()
        || subclass.access_flags & (ENUM | FINAL) != ENUM | FINAL
        || pool.class_name(subclass.super_class)? != owner
    {
        return Err(fail());
    }
    let Some(constructor) = find_constructor(subclass, descriptor)? else {
        return Err(fail());
    };
    for method in &subclass.methods {
        if !std::ptr::eq(method, constructor) && pool.utf8(method.name_index)? == "<init>" {
            return Err(fail());
        }
    }
    let code = constructor.code(pool)?.ok_or_else(fail)?;
    let instructions = decode(code.bytes).map_err(|_| fail())?;
    let args_end = 1 + ty.parameters.len();
    let (loads, tail) = instructions.split_at_checked(args_end).ok_or_else(fail)?;
    if !forwards(loads, &ty.parameters) {
        return Err(fail());
    }
    let has_dummy = tail.first().is_some_and(|op| op.opcode == 0x01);
    let call = tail.get(usize::from(has_dummy)).ok_or_else(fail)?;
    let Some((target, "<init>", target_descriptor)) = member(subclass, call, 0xb7)? else {
        return Err(fail());
    };
    if target != owner || !target_descriptor.starts_with(CONSTRUCTOR_PREFIX) {
        return Err(fail());
    }
    let bridge = if has_dummy {
        if !verify_bridge(parent, owner, target_descriptor, descriptor, ty)? {
            return Err(fail());
        }
        let method = find_constructor(parent, target_descriptor)?.ok_or_else(fail)?;
        // Return the parent's descriptor, rather than requiring the child pool's
        // lifetime when the body site and its bridge visibility are separated.
        Some(parent.pool.utf8(method.descriptor_index)?)
    } else {
        if target_descriptor != descriptor {
            return Err(fail());
        }
        None
    };
    let constructor = find_constructor(parent, descriptor)?.ok_or_else(fail)?;
    if constructor.access_flags & (SYNTHETIC | STATIC) != 0 {
        return Err(fail());
    }
    let start = args_end + usize::from(has_dummy) + 1;
    let initializer = &instructions[start..];
    let offset = initializer.first().ok_or_else(fail)?.offset;
    let end_params = 1 + ty.parameters.iter().map(Type::slots).sum::<u16>();
    if initializer
        .iter()
        .any(|op| local_slot(op).is_some_and(|slot| (1..end_params).contains(&slot)))
        || enters_prefix(&code, initializer, offset)
    {
        return Err(fail());
    }
    let site = AnonymousSite::uncaptured(allocated, descriptor, instructions, start);
    Ok(ConstantSubclass { site, bridge })
}

pub(super) fn find_constructor<'c, 'a>(
    class: &'c ClassFile<'a>,
    descriptor: &str,
) -> Result<Option<&'c Member<'a>>, DecompileError> {
    let mut found = None;
    for method in &class.methods {
        if class.pool.utf8(method.name_index)? == "<init>"
            && class.pool.utf8(method.descriptor_index)? == descriptor
        {
            if found.replace(method).is_some() || method.access_flags & STATIC != 0 {
                return Err(unsupported("ambiguous enum constructor"));
            }
        }
    }
    Ok(found)
}

fn verify_bridge(
    class: &ClassFile<'_>,
    owner: &str,
    bridge: &str,
    target: &str,
    ty: &MethodDescriptor,
) -> Result<bool, DecompileError> {
    let Some(method) = find_constructor(class, bridge)? else {
        return Ok(false);
    };
    if method.access_flags & SYNTHETIC == 0 || method.access_flags & !(SYNTHETIC | PRIVATE) != 0 {
        return Ok(false);
    }
    let bridge_type = parse(bridge, MethodDescriptor::parse)?;
    let Some((Type::Object(dummy), leading)) = bridge_type.parameters.split_last() else {
        return Ok(false);
    };
    if !dummy.rsplit_once('$').is_some_and(|(_, index)| {
        !index.is_empty() && index.bytes().all(|byte| byte.is_ascii_digit())
    }) || leading != ty.parameters.as_slice()
        || bridge_type.return_type != Type::Void
    {
        return Ok(false);
    }
    let Some(code) = method.code(&class.pool)? else {
        return Ok(false);
    };
    let instructions =
        decode(code.bytes).map_err(|_| unsupported("nonstandard enum constructor bridge"))?;
    let [loads @ .., call, ret] = instructions.as_slice() else {
        return Ok(false);
    };
    Ok(code.exceptions.is_empty()
        && forwards(loads, leading)
        && ret.opcode == 0xb1
        && member(class, call, 0xb7)? == Some((owner, "<init>", target)))
}

fn forwards(loads: &[Instruction], args: &[Type]) -> bool {
    let Some((receiver, loads)) = loads.split_first() else {
        return false;
    };
    if !local(receiver, 0x19, 0) || loads.len() != args.len() {
        return false;
    }
    let mut slot = 1;
    for (op, ty) in loads.iter().zip(args) {
        let opcode = match ty {
            Type::Object(_) | Type::Array(_) => 0x19,
            Type::Primitive(Primitive::Long) => 0x16,
            Type::Primitive(Primitive::Float) => 0x17,
            Type::Primitive(Primitive::Double) => 0x18,
            Type::Primitive(_) => 0x15,
            Type::Void => return false,
        };
        if !local(op, opcode, slot) {
            return false;
        }
        slot += ty.slots();
    }
    true
}

/// Whether any independent control-flow edge enters a removed prologue.
pub(super) fn enters_prefix(code: &Code<'_>, tail: &[Instruction], start: u32) -> bool {
    code.exceptions
        .iter()
        .any(|ex| u32::from(ex.start_pc) < start || u32::from(ex.handler_pc) < start)
        || tail.iter().any(|op| match &op.operand {
            Operand::Branch(target) => *target < start,
            Operand::Switch { default, cases } => {
                *default < start || cases.iter().any(|&(_, target)| target < start)
            }
            _ => false,
        })
}

pub(super) fn local_slot(op: &Instruction) -> Option<u16> {
    match op.operand {
        Operand::Local(slot) | Operand::Increment { index: slot, .. } => Some(slot),
        _ => match op.opcode {
            0x1a..=0x2d => Some(u16::from((op.opcode - 0x1a) % 4)),
            0x3b..=0x4e => Some(u16::from((op.opcode - 0x3b) % 4)),
            _ => None,
        },
    }
}
