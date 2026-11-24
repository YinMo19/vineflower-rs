// Based on Vineflower enum handling in ClassWriter and InitializerProcessor (Apache-2.0).
use std::fmt::Write;

use super::{DecompileError, ENUM, FINAL, PRIVATE, PUBLIC, STATIC, SYNTHETIC, parse};
use crate::{
    bytecode::{Instruction, Operand, decode},
    classfile::{ClassFile, Constant, Member},
    descriptor::{MethodDescriptor, Type},
    lift::constant_literal,
};

const CONSTRUCTOR_PREFIX: &str = "(Ljava/lang/String;I";

pub(super) struct Enumeration<'a> {
    names: Vec<&'a str>,
    declarations: Vec<String>,
    values_field: Option<&'a str>,
    helper: Option<&'a str>,
    skip_initializer: usize,
}

impl<'a> Enumeration<'a> {
    pub(super) fn recover(class: &'a ClassFile<'_>, ascii: bool) -> Result<Self, DecompileError> {
        let pool = &class.pool;
        if class.super_class == 0 || pool.class_name(class.super_class)? != "java/lang/Enum" {
            return Err(unsupported("enum with nonstandard superclass"));
        }
        let owner = pool.class_name(class.this_class)?;
        let values_type = format!("[L{owner};");
        let field_type = &values_type[1..];
        let mut names = Vec::new();
        let mut values_field = None;
        for field in &class.fields {
            let name = pool.utf8(field.name_index)?;
            if field.access_flags & ENUM != 0 {
                names.push(name);
            } else if field.access_flags & (PRIVATE | STATIC | FINAL | SYNTHETIC)
                == PRIVATE | STATIC | FINAL | SYNTHETIC
                && pool.utf8(field.descriptor_index)? == values_type
                && values_field.replace(name).is_some()
            {
                return Err(unsupported("ambiguous enum values arrays"));
            }
        }
        let initializer = class
            .methods
            .iter()
            .find(|method| matches!(pool.utf8(method.name_index), Ok("<clinit>")));
        let mut result = Self {
            names,
            declarations: Vec::new(),
            values_field,
            helper: None,
            skip_initializer: 0,
        };
        let Some(initializer) = initializer else {
            // Some assemblers provide enum-flagged fields without a generated initializer.
            result
                .declarations
                .extend(result.names.iter().map(|name| (*name).into()));
            return Ok(result);
        };
        let values =
            values_field.ok_or_else(|| unsupported("enum without synthetic values array"))?;
        let code = initializer
            .code(pool)?
            .ok_or(DecompileError::InvalidAttribute(
                "enum class initializer Code",
            ))?;
        let instructions = decode(code.bytes).map_err(|source| DecompileError::Method {
            name: "<clinit>".into(),
            descriptor: "()V".into(),
            source: Box::new(source),
        })?;
        let mut cursor = instructions.as_slice();
        for (ordinal, &name) in result.names.iter().enumerate() {
            let Some(([new, duplicate, name_load, order], tail)) = cursor.split_first_chunk::<4>()
            else {
                return Err(pattern());
            };
            if !class_is(class, new, 0xbb, owner)?
                || duplicate.opcode != 0x59
                || string_value(class, name_load)? != Some(name)
                || integer(class, order)? != Some(ordinal as i32)
            {
                return Err(unsupported(
                    "enum constants with custom subclasses or initialization",
                ));
            }
            let constructor_at = tail
                .iter()
                .position(|op| op.opcode == 0xb7)
                .ok_or_else(pattern)?;
            let call = &tail[constructor_at];
            let Some((call_owner, "<init>", raw)) = member(class, call, 0xb7)? else {
                return Err(pattern());
            };
            if call_owner != owner || !raw.starts_with(CONSTRUCTOR_PREFIX) {
                return Err(pattern());
            }
            let descriptor = parse(raw, MethodDescriptor::parse)?;
            let arguments = &descriptor.parameters[2..];
            if arguments.len() != constructor_at || descriptor.return_type != Type::Void {
                return Err(unsupported("nonliteral enum arguments"));
            }
            let mut declaration = String::from(name);
            if !arguments.is_empty() {
                declaration.push('(');
                for (index, (ty, op)) in arguments.iter().zip(tail).enumerate() {
                    if index != 0 {
                        declaration.push_str(", ");
                    }
                    if let Some(value) = integer(class, op)? {
                        match ty {
                            Type::Primitive(crate::descriptor::Primitive::Boolean)
                                if matches!(value, 0 | 1) =>
                            {
                                declaration.push_str(if value != 0 { "true" } else { "false" });
                            }
                            Type::Primitive(crate::descriptor::Primitive::Byte) => {
                                let _ = write!(declaration, "(byte){value}");
                            }
                            Type::Primitive(crate::descriptor::Primitive::Short) => {
                                let _ = write!(declaration, "(short){value}");
                            }
                            Type::Primitive(crate::descriptor::Primitive::Char) => {
                                let _ = write!(declaration, "(char){value}");
                            }
                            Type::Primitive(crate::descriptor::Primitive::Int) => {
                                let _ = write!(declaration, "{value}");
                            }
                            _ => return Err(unsupported("nonliteral enum arguments")),
                        }
                    } else if op.opcode == 0x01 && matches!(ty, Type::Object(_) | Type::Array(_)) {
                        // A bare null could resolve to a different constructor overload.
                        return Err(unsupported("null enum constructor argument"));
                    } else if let Some(index) = load_constant(op) {
                        declaration.push_str(
                            &constant_literal(pool, index, Some(ty), ascii).map_err(|source| {
                                DecompileError::Render {
                                    context: "enum argument",
                                    source: Box::new(source),
                                }
                            })?,
                        );
                    } else {
                        declaration.push_str(match op.opcode {
                            0x09 => "0L",
                            0x0a => "1L",
                            0x0b => "0.0F",
                            0x0c => "1.0F",
                            0x0d => "2.0F",
                            0x0e => "0.0",
                            0x0f => "1.0",
                            _ => return Err(unsupported("nonliteral enum arguments")),
                        });
                    }
                }
                declaration.push(')');
            }
            let store = tail.get(constructor_at + 1).ok_or_else(pattern)?;
            if member(class, store, 0xb3)? != Some((owner, name, field_type)) {
                return Err(pattern());
            }
            result.declarations.push(declaration);
            cursor = &tail[constructor_at + 2..];
        }
        let values_method = format!("(){values_type}");
        if let Some((helper_owner, helper, desc)) =
            member(class, cursor.first().ok_or_else(pattern)?, 0xb8)?
        {
            if helper_owner != owner || desc != values_method {
                return Err(pattern());
            }
            let mut found = false;
            for method in &class.methods {
                if method.access_flags & (PRIVATE | STATIC | SYNTHETIC)
                    == PRIVATE | STATIC | SYNTHETIC
                    && pool.utf8(method.name_index)? == helper
                    && pool.utf8(method.descriptor_index)? == values_method
                {
                    let code = method.code(pool)?.ok_or_else(pattern)?;
                    let instructions = decode(code.bytes).map_err(|_| pattern())?;
                    let tail = values_array(class, &result.names, field_type, &instructions)?;
                    found =
                        matches!(tail, [ret] if ret.opcode == 0xb0) && code.exceptions.is_empty();
                    break;
                }
            }
            if !found {
                return Err(pattern());
            }
            result.helper = Some(helper);
            cursor = &cursor[1..];
        } else {
            cursor = values_array(class, &result.names, field_type, cursor)?;
        }
        let Some((store, tail)) = cursor.split_first() else {
            return Err(pattern());
        };
        if member(class, store, 0xb3)? != Some((owner, values, values_type.as_str()))
            || tail.is_empty()
        {
            return Err(pattern());
        }
        result.skip_initializer = instructions.len() - tail.len();
        let start = tail[0].offset;
        if code
            .exceptions
            .iter()
            .any(|ex| u32::from(ex.start_pc) < start || u32::from(ex.handler_pc) < start)
        {
            return Err(unsupported("exception handler covers enum construction"));
        }
        Ok(result)
    }

    pub(super) fn declarations(&self) -> &[String] {
        &self.declarations
    }

    pub(super) fn hides_field(&self, field: &Member<'_>, name: &str) -> bool {
        field.access_flags & ENUM != 0 || self.values_field == Some(name)
    }

    pub(super) fn hides_method(
        &self,
        owner: &str,
        name: &str,
        desc: &str,
        method: &Member<'_>,
    ) -> bool {
        self.helper == Some(name)
            && method.access_flags & (PRIVATE | STATIC | SYNTHETIC) == PRIVATE | STATIC | SYNTHETIC
            || method.access_flags & (PUBLIC | STATIC) == PUBLIC | STATIC
                && match name {
                    "values" => {
                        desc.strip_prefix("()[L")
                            .and_then(|desc| desc.strip_suffix(';'))
                            == Some(owner)
                    }
                    "valueOf" => {
                        desc.strip_prefix("(Ljava/lang/String;)L")
                            .and_then(|desc| desc.strip_suffix(';'))
                            == Some(owner)
                    }
                    _ => false,
                }
    }

    pub(super) fn method_prefix(
        &self,
        class: &ClassFile<'_>,
        name: &str,
        desc: &str,
        instructions: &[Instruction],
    ) -> Result<usize, DecompileError> {
        match name {
            "<clinit>" => Ok(self.skip_initializer),
            "<init>" if desc.starts_with(CONSTRUCTOR_PREFIX) => {
                let Some(([receiver, label, position, super_call], tail)) =
                    instructions.split_first_chunk::<4>()
                else {
                    return Err(pattern());
                };
                let init = member(class, super_call, 0xb7)?;
                if !local(receiver, 0x19, 0)
                    || !local(label, 0x19, 1)
                    || !local(position, 0x15, 2)
                    || init != Some(("java/lang/Enum", "<init>", "(Ljava/lang/String;I)V"))
                    || tail.is_empty()
                {
                    return Err(unsupported("enum constructor delegation"));
                }
                // A source enum cannot read the two implicit constructor parameters.
                if tail
                    .iter()
                    .any(|insn| local(insn, 0x19, 1) || local(insn, 0x15, 2))
                {
                    return Err(unsupported(
                        "explicit use of JVM enum constructor parameters",
                    ));
                }
                Ok(4)
            }
            "<init>" => Err(pattern()),
            _ => Ok(0),
        }
    }
}

fn values_array<'i>(
    class: &ClassFile<'_>,
    names: &[&str],
    field_type: &str,
    instructions: &'i [Instruction],
) -> Result<&'i [Instruction], DecompileError> {
    let owner = class.pool.class_name(class.this_class)?;
    let Some(([length, new], mut tail)) = instructions.split_first_chunk::<2>() else {
        return Err(pattern());
    };
    if integer(class, length)? != Some(names.len() as i32) || !class_is(class, new, 0xbd, owner)? {
        return Err(pattern());
    }
    for (index, &name) in names.iter().enumerate() {
        let Some(([reference, slot, load, store], rest)) = tail.split_first_chunk::<4>() else {
            return Err(pattern());
        };
        if reference.opcode != 0x59
            || integer(class, slot)? != Some(index as i32)
            || member(class, load, 0xb2)? != Some((owner, name, field_type))
            || store.opcode != 0x53
        {
            return Err(pattern());
        }
        tail = rest;
    }
    Ok(tail)
}

fn load_constant(op: &Instruction) -> Option<u16> {
    match (op.opcode, &op.operand) {
        (0x12..=0x14, Operand::Constant(index)) => Some(*index),
        _ => None,
    }
}

fn string_value<'a>(
    class: &'a ClassFile<'_>,
    op: &Instruction,
) -> Result<Option<&'a str>, DecompileError> {
    Ok(
        match load_constant(op)
            .map(|index| class.pool.get(index))
            .transpose()?
        {
            Some(Constant::String(index)) => Some(class.pool.utf8(*index)?),
            _ => None,
        },
    )
}

fn integer(class: &ClassFile<'_>, op: &Instruction) -> Result<Option<i32>, DecompileError> {
    Ok(match (op.opcode, &op.operand) {
        (0x02..=0x08, _) => Some(i32::from(op.opcode) - 3),
        (0x10..=0x11, Operand::Immediate(value)) => Some(*value),
        (0x12..=0x13, Operand::Constant(index)) => match class.pool.get(*index)? {
            Constant::Integer(value) => Some(*value),
            _ => None,
        },
        _ => None,
    })
}

fn class_is(
    class: &ClassFile<'_>,
    op: &Instruction,
    opcode: u8,
    expected: &str,
) -> Result<bool, DecompileError> {
    match (op.opcode, &op.operand) {
        (code, Operand::Constant(index)) if code == opcode => {
            Ok(class.pool.class_name(*index)? == expected)
        }
        _ => Ok(false),
    }
}

fn member<'a>(
    class: &'a ClassFile<'_>,
    op: &Instruction,
    opcode: u8,
) -> Result<Option<(&'a str, &'a str, &'a str)>, DecompileError> {
    match (op.opcode, &op.operand) {
        (code, Operand::Constant(index)) if code == opcode => {
            Ok(Some(class.pool.member_ref(*index)?))
        }
        _ => Ok(None),
    }
}

fn local(op: &Instruction, opcode: u8, slot: u16) -> bool {
    (op.opcode == opcode && op.operand == Operand::Local(slot))
        || (slot < 4 && op.opcode == 0x1a + (opcode - 0x15) * 4 + slot as u8)
}

fn pattern() -> DecompileError {
    unsupported("nonstandard enum initialization")
}
fn unsupported(feature: &'static str) -> DecompileError {
    DecompileError::Unsupported { feature }
}
