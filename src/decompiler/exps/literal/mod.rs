// Copyright 2000-2018 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Java source and source-map tokens for ConstExprent and annotation values.

mod decimal;
mod symbols;

pub use symbols::precedence;

use super::{BytecodeOffsets, ConstantValue};
use crate::engine::{Cx, import_collector};
use crate::types::{CodeType, FieldDescriptor, VarType};
use crate::util::{
    java_str::JavaString,
    text_buffer::TextBuffer,
    text_util::{char_to_unicode_literal, is_printable_unicode},
};
use std::io;

/// Render a constant with its inferred type and original bytecode positions.
pub fn render(
    cx: &mut Cx,
    ty: &VarType,
    value: &ConstantValue,
    offsets: Option<&BytecodeOffsets>,
    was_condy: bool,
) -> io::Result<TextBuffer> {
    use CodeType::*;
    let mut buf = TextBuffer::new(cx);
    add_offsets(&mut buf, offsets);
    if was_condy {
        buf.append("/* $VF: constant dynamic */ ");
    }
    if *value == ConstantValue::Null && ty.ty != Null {
        buf.append_cast_type_name(cx, ty);
        return Ok(buf);
    }
    let literal = cx.options.keep_literals;
    let unboxed = ty.unboxing_type().map_or(ty.ty, |ty| ty.ty);
    match (unboxed, value) {
        (Boolean, ConstantValue::Integer(n)) => {
            buf.append(if *n == 0 { "false" } else { "true" });
        }
        (Char, ConstantValue::Integer(n)) => {
            let mut text = String::new();
            if let Ok(unit) = u16::try_from(*n) {
                escaped_unit(&mut text, unit, b'\'', cx.options.ascii_strings);
            } else {
                // CHAR_ESCAPES is keyed by the original int before Java narrows it.
                push_char(&mut text, *n as u16, cx.options.ascii_strings);
            }
            buf.append(&text).enclose("'", "'");
        }
        (Byte | Bytechar | Shortchar | Short | Int, ConstantValue::Integer(n)) => {
            match (literal, *n) {
                (false, i32::MAX) => {
                    symbols::Field::integer("MAX_VALUE").write(cx, &mut buf, offsets)
                }
                (false, i32::MIN) => {
                    symbols::Field::integer("MIN_VALUE").write(cx, &mut buf, offsets)
                }
                _ => {
                    buf.append_int(*n);
                }
            }
        }
        (Long, ConstantValue::Long(n)) => match (literal, *n) {
            (false, i64::MAX) => symbols::Field::long("MAX_VALUE").write(cx, &mut buf, offsets),
            (false, i64::MIN) => symbols::Field::long("MIN_VALUE").write(cx, &mut buf, offsets),
            _ => {
                buf.append(&n.to_string()).append_char('L');
            }
        },
        (Float, ConstantValue::Float(x)) => {
            if !literal && symbols::write_float(cx, &mut buf, *x, offsets) {
                return Ok(buf);
            }
            if x.is_finite() {
                buf.append(&decimal::float(*x)).append_char('F');
            } else {
                buf.append(if x.is_nan() {
                    "0.0F / 0.0F"
                } else if x.is_sign_negative() {
                    "-1.0F / 0.0F"
                } else {
                    "1.0F / 0.0F"
                });
            }
        }
        (Double, ConstantValue::Double(x)) => {
            if !literal && symbols::write_double(cx, &mut buf, *x, offsets) {
                return Ok(buf);
            }
            if x.is_finite() {
                let double = decimal::double(*x);
                let single = *x as f32;
                if !literal
                    && f64::from(single) == *x
                    && let short = decimal::float(single)
                    && short.len() < double.len()
                {
                    if !symbols::write_float(cx, &mut buf, single, offsets) {
                        buf.append(&short).append_char('F');
                    }
                } else {
                    buf.append(&double);
                }
            } else {
                buf.append(if x.is_nan() {
                    "0.0 / 0.0"
                } else if x.is_sign_negative() {
                    "-1.0 / 0.0"
                } else {
                    "1.0 / 0.0"
                });
            }
        }
        (Null, _) => {
            buf.append("null");
        }
        (Object, ConstantValue::String(text)) if *ty == VarType::VARTYPE_STRING => {
            buf.append(&escape_string(text, cx.options.ascii_strings))
                .enclose("\"", "\"");
        }
        (Object, ConstantValue::String(text)) if *ty == VarType::VARTYPE_CLASS => {
            let name = text.as_utf8_lossy();
            let class = VarType::from_signature_cl(name, !name.starts_with('['));
            buf.append_cast_type_name(cx, &class).append(".class");
        }
        (Object, ConstantValue::String(text)) if *ty == VarType::VARTYPE_METHODTYPE => {
            if cx.options.decompiler_comments {
                buf.append("/* $VF: MethodType constant */ ");
            }
            import_collector::get_short_name(cx, "java.lang.invoke.MethodType");
            buf.append("MethodType.fromMethodDescriptorString(\"")
                .append(text.as_utf8_lossy())
                .append("\", null)");
        }
        _ => {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("Invalid constant type {ty} with value {value:?}"),
            ));
        }
    }
    Ok(buf)
}

fn add_offsets(buf: &mut TextBuffer, offsets: Option<&BytecodeOffsets>) {
    for offset in offsets.into_iter().flat_map(BytecodeOffsets::iter) {
        buf.add_bytecode_mapping(offset as i32);
    }
}

fn escape_string(value: &JavaString, ascii: bool) -> String {
    let mut text = String::new();
    for unit in value.utf16() {
        escaped_unit(&mut text, unit, b'"', ascii);
    }
    text
}

fn escaped_unit(text: &mut String, unit: u16, quote: u8, ascii: bool) {
    text.push_str(match unit {
        0x08 => "\\b",
        0x09 => "\\t",
        0x0a => "\\n",
        0x0c => "\\f",
        0x0d => "\\r",
        0x5c => "\\\\",
        0x22 if quote == b'"' => "\\\"",
        0x27 if quote == b'\'' => "\\'",
        _ => {
            push_char(text, unit, ascii);
            return;
        }
    });
}

fn push_char(text: &mut String, unit: u16, ascii: bool) {
    if (32..127).contains(&unit) || !ascii && is_printable_unicode(unit) {
        text.push(char::from_u32(u32::from(unit)).expect("Printable BMP character"));
    } else {
        text.push_str(&char_to_unicode_literal(i32::from(unit)));
    }
}

/// Render a static field reference whose descriptor and name are already known.
pub(crate) fn static_field(
    cx: &mut Cx,
    owner: &str,
    name: &str,
    descriptor: &FieldDescriptor,
    offsets: Option<&BytecodeOffsets>,
) -> TextBuffer {
    let mut buf = TextBuffer::new(cx);
    if name == "TYPE" {
        let wrapper = VarType::from_signature_cl(owner, true);
        let primitive = wrapper
            .unboxing_type()
            .or_else(|| (owner == "java/lang/Void").then_some(VarType::VARTYPE_VOID));
        if let Some(primitive) = primitive {
            buf.append_cast_type_name(cx, &primitive).append(".class");
            return buf;
        }
    }
    let ambiguous = cx
        .writing_method()
        .and_then(|method| method.method.get_local_variable_attr())
        .is_some_and(|lvt| lvt.contains_name(name));
    if cx.current_class_node.as_deref() != Some(owner) || ambiguous {
        let dotted = import_collector::java_class_name(cx, owner);
        let short = import_collector::get_short_name_in_class_context(cx, &dotted);
        buf.append_all_classes(&short, owner).append_char('.');
    }
    add_offsets(&mut buf, offsets);
    buf.append_field_with(name, false, owner, name, descriptor.clone());
    buf
}
