// SPDX-License-Identifier: Apache-2.0

//! KNewExprent's constructor and array output.

use std::io;

use crate::decompiler::exps::{ExprKind, WriteFlags, literal, write};
use crate::decompiler::ir::ExprId;
use crate::engine::Cx;
use crate::kotlin::types::kotlin_type;
use crate::types::{CodeType, VarType};
use crate::util::text_buffer::TextBuffer;

pub(super) fn allocation(
    cx: &mut Cx,
    expr: ExprId,
    indent: i32,
    in_annotation: bool,
) -> io::Result<TextBuffer> {
    if let Some(value) = crate::kotlin::writer::allocation_expression(cx, expr, indent)? {
        return Ok(value);
    }
    let ExprKind::New {
        new_type,
        dimensions,
        constructor,
        array_elements,
        ..
    } = &cx.ir[expr].kind
    else {
        unreachable!()
    };
    let (ty, constructor) = (new_type.clone(), *constructor);
    let flags = cx.ir[expr].write_flags;
    let mut result = TextBuffer::new(cx);
    if ty.array_dim == 0 {
        let enum_const = flags.contains(WriteFlags::ENUM_CONST);
        if !enum_const {
            let mut name = kotlin_type(cx, Some(&ty), true)?;
            if let Some(constructor) = constructor {
                let first = call(cx, constructor)?.parameters.first().copied();
                if let Some(enclosing) =
                    write::qualified_new_instance(cx, ty.name(), first, indent)?
                {
                    result.append_buffer(&enclosing).append_char('.');
                    name = cx
                        .class_nodes
                        .get(ty.name())
                        .and_then(|node| node.simple_name.as_deref())
                        .unwrap_or_else(|| name.rsplit('.').next().unwrap())
                        .to_owned();
                }
            }
            result.append_type_name_with(cx, &name, &ty);
        }
        if let Some(constructor) = constructor
            && (!enum_const || call(cx, constructor)?.parameters.len() > 2)
        {
            let args = call(cx, constructor)?
                .generics
                .as_ref()
                .map_or_else(Vec::new, |args| args.arguments.clone());
            if !args.is_empty() {
                result.append_char('<');
                for (index, ty) in args.iter().enumerate() {
                    if index > 0 {
                        result.append(", ");
                    }
                    result.append_cast_type_name(cx, ty);
                }
                result.append_char('>');
            }
            result
                .append_char('(')
                .append_buffer(&write::append_param_list(cx, constructor, indent)?)
                .append_char(')');
        }
    } else if flags.contains(WriteFlags::VARARG) {
        let elements = array_elements.clone();
        append_elements(cx, &mut result, indent, &elements, false)?;
    } else if in_annotation {
        let elements = array_elements.clone();
        result
            .append_char('[')
            .push_newline_group(indent, 1)
            .append_possible_newline();
        append_elements(cx, &mut result, indent, &elements, true)?;
        result
            .append_possible_newline_or("", true)
            .pop_newline_group()
            .append_char(']');
    } else if array_elements.is_empty() {
        let dimensions = dimensions.clone();
        let rank = ty.array_dim as usize;
        for index in 0..rank {
            if index + 1 < rank {
                result.append("Array(");
            } else {
                result.append(array_constructor(ty.ty)).append_char('(');
            }
            let Some(&dim) = dimensions.get(index) else {
                return Err(invalid("Kotlin array allocation has no dimension"));
            };
            literal::adjust_const_type(&mut cx.ir, dim, &VarType::VARTYPE_INT);
            result.append_buffer(&write::to_java(cx, dim, indent)?);
            if index + 1 < rank {
                result
                    .append(") {")
                    .push_newline_group(indent, 1)
                    .append_possible_newline_or(" ", false);
            } else {
                result.append_char(')');
            }
        }
        for _ in 1..rank {
            result
                .append_possible_newline_or(" ", true)
                .pop_newline_group()
                .append_char('}');
        }
    } else {
        let elements = array_elements.clone();
        result
            .append(array_factory(ty.decrease_array_dim().ty))
            .append_char('(')
            .push_newline_group(indent, 1)
            .append_possible_newline();
        append_elements(cx, &mut result, indent, &elements, false)?;
        result
            .append_possible_newline_or("", true)
            .pop_newline_group()
            .append_char(')');
    }
    Ok(result)
}

fn append_elements(
    cx: &mut Cx,
    result: &mut TextBuffer,
    indent: i32,
    elements: &[ExprId],
    in_annotation: bool,
) -> io::Result<()> {
    for (index, &element) in elements.iter().enumerate() {
        if index > 0 {
            result
                .append_char(',')
                .append_possible_newline_or(" ", false);
        }
        if in_annotation {
            super::set_in_annotation(cx, element);
        }
        result.append_buffer(&write::to_java(cx, element, indent)?);
    }
    Ok(())
}

fn array_constructor(ty: CodeType) -> &'static str {
    match ty {
        CodeType::Boolean => "BooleanArray",
        CodeType::Byte => "ByteArray",
        CodeType::Short => "ShortArray",
        CodeType::Char => "CharArray",
        CodeType::Int => "IntArray",
        CodeType::Float => "FloatArray",
        CodeType::Long => "LongArray",
        CodeType::Double => "DoubleArray",
        _ => "arrayOfNulls",
    }
}

fn array_factory(ty: CodeType) -> &'static str {
    match ty {
        CodeType::Boolean => "booleanArrayOf",
        CodeType::Byte => "byteArrayOf",
        CodeType::Short => "shortArrayOf",
        CodeType::Char => "charArrayOf",
        CodeType::Int => "intArrayOf",
        CodeType::Float => "floatArrayOf",
        CodeType::Long => "longArrayOf",
        CodeType::Double => "doubleArrayOf",
        _ => "arrayOf",
    }
}

fn call(cx: &Cx, expr: ExprId) -> io::Result<&crate::decompiler::exps::Invocation> {
    let ExprKind::Invocation(invoke) = &cx.ir[expr].kind else {
        return Err(invalid("Kotlin constructor must be an invocation"));
    };
    Ok(invoke)
}

fn invalid(message: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}
