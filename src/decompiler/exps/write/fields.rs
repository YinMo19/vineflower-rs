// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Java field expressions and member qualification.

use std::io;

use super::{
    casts::{CastOptions, NullCastType, append_casted},
    precedence,
};
use crate::decompiler::exps::{Expr, ExprKind, FunctionType, WriteFlags, literal};
use crate::decompiler::ir::ExprId;
use crate::engine::{Cx, import_collector};
use crate::types::{CodeType, VarType};
use crate::util::text_buffer::TextBuffer;

pub(super) fn to_java(cx: &mut Cx, expr: ExprId, indent: i32) -> io::Result<TextBuffer> {
    let ExprKind::Field(field) = &cx.ir[expr].kind else {
        unreachable!()
    };
    let field = field.clone();
    let owner = field
        .classname
        .as_deref()
        .ok_or_else(|| invalid("Field has no declaring class"))?;
    let offsets = cx.ir[expr].bytecode.clone();
    let mut buffer = TextBuffer::new(cx);
    if field.was_condy {
        buffer.append("/* $VF: constant dynamic */ ");
    }

    let Some(instance) = field.instance else {
        literal::append_static_field(
            cx,
            &mut buffer,
            owner,
            &field.name,
            &field.descriptor,
            offsets.as_ref(),
            field.force_qualified,
        );
        return Ok(buffer);
    };

    let qualifier = Expr::variable(&cx.ir, instance)
        .and_then(|var| {
            let method = cx.writing_method()?;
            cx.ir[method.variables].this_vars.get(&var.pair())
        })
        .filter(|&name| name.as_str() != owner)
        .cloned();
    if let Some(qualifier) = qualifier {
        write_qualified_super(cx, &mut buffer, &qualifier)?;
    } else {
        let group = !cx.ir[expr].write_flags.contains(WriteFlags::QUALIFIER);
        if group {
            buffer.push_newline_group(indent, 1);
        }
        mark_qualifier(cx, instance);
        let mut receiver = TextBuffer::new(cx);
        let expected = VarType::with_value(CodeType::Object, 0, owner);
        let cast = append_casted(
            cx,
            instance,
            &expected,
            &mut receiver,
            indent,
            CastOptions {
                null_cast: NullCastType::Cast,
                cast_always: false,
                cast_narrowing: false,
                unbox: false,
            },
        )?;
        if cast || precedence(cx, instance)? > precedence(cx, expr)? {
            receiver.enclose_with_parens();
        }
        buffer.append_buffer(&receiver);
        if allows_newline_after_qualifier(cx, instance) {
            buffer.append_possible_newline();
        }
        if group {
            buffer.pop_newline_group();
        }
    }

    if buffer.content_equals(super::variables::NAMELESS_ENCLOSURE) {
        buffer.set_length(0);
    } else {
        buffer.append_char('.');
    }

    literal::add_offsets(&mut buffer, offsets.as_ref());
    buffer.append_field_with(&field.name, false, owner, &field.name, field.descriptor);
    Ok(buffer)
}

/// Exprent.setIsQualifier follows casts that will be omitted.
pub(super) fn mark_qualifier(cx: &mut Cx, mut expr: ExprId) {
    loop {
        match &cx.ir[expr].kind {
            ExprKind::Field(_) | ExprKind::Invocation(_) => {
                cx.ir[expr].write_flags.insert(WriteFlags::QUALIFIER);
                return;
            }
            ExprKind::Function {
                op: FunctionType::Cast,
                operands,
                needs_cast: false,
                ..
            } => {
                expr = operands[0];
            }
            _ => return,
        }
    }
}

pub(super) fn allows_newline_after_qualifier(cx: &Cx, mut expr: ExprId) -> bool {
    loop {
        match &cx.ir[expr].kind {
            ExprKind::Variable(_) => return false,
            ExprKind::Field(field) if field.is_static() => {
                return field.classname.as_ref().is_none_or(|owner| {
                    literal::uses_qualified_static(cx, owner, &field.name, field.force_qualified)
                });
            }
            ExprKind::Function {
                op: FunctionType::Cast,
                operands,
                needs_cast: false,
                ..
            } => {
                expr = operands[0];
            }
            _ => return true,
        }
    }
}

pub(super) fn write_qualified_super(
    cx: &mut Cx,
    buffer: &mut TextBuffer,
    qualifier: &str,
) -> io::Result<()> {
    let current = cx
        .current_class_node
        .as_deref()
        .ok_or_else(|| invalid("No current class for super qualifier"))?;
    if qualifier != current {
        let dotted = import_collector::java_class_name(cx, qualifier);
        let short = import_collector::get_short_name(cx, &dotted);
        buffer
            .append_all_classes(&short, qualifier)
            .append_char('.');
    }
    buffer.append("super");
    Ok(())
}

fn invalid(message: &str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}
