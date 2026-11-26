// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! The annotation-independent comments written by ClassWriter.

use std::io;

use crate::decompiler::expr_processor::cast_type_name;
use crate::engine::{Cx, import_collector::java_class_name};
use crate::types::{FieldDescriptor, MethodDescriptor, VarType};
use crate::util::text_buffer::TextBuffer;

pub(super) enum RenameKind {
    Class,
    Field,
    Method,
}

pub(super) fn append_rename_comment(
    cx: &mut Cx,
    buffer: &mut TextBuffer,
    old_name: Option<&str>,
    kind: RenameKind,
    indent: i32,
) -> io::Result<()> {
    let Some(old_name) = old_name else {
        return Ok(());
    };
    buffer
        .append_indent(indent)
        .append("// $VF: renamed from: ");
    match kind {
        RenameKind::Class => {
            buffer.append(&java_class_name(cx, old_name));
        }
        RenameKind::Field | RenameKind::Method => {
            let mut parts = old_name.split(' ').skip(1);
            let (Some(name), Some(descriptor)) = (parts.next(), parts.next()) else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "Invalid original member name",
                ));
            };
            buffer.append(name).append_char(' ');
            match kind {
                RenameKind::Field => {
                    let descriptor = FieldDescriptor::parse_descriptor(descriptor);
                    buffer.append(&display_type(cx, &descriptor.ty));
                }
                RenameKind::Method => {
                    let descriptor = MethodDescriptor::parse_descriptor(descriptor);
                    buffer.append_char('(');
                    for (i, ty) in descriptor.params.iter().enumerate() {
                        if i > 0 {
                            buffer.append(", ");
                        }
                        buffer.append(&display_type(cx, ty));
                    }
                    buffer
                        .append(") ")
                        .append(&display_type(cx, &descriptor.ret));
                }
                RenameKind::Class => unreachable!(),
            }
        }
    }
    buffer.append_line_separator();
    Ok(())
}

fn display_type(cx: &mut Cx, ty: &VarType) -> String {
    let name = cast_type_name(cx, ty, false);
    if name == "<undefinedtype>" && cx.options.undefined_as_object {
        cast_type_name(cx, &VarType::VARTYPE_OBJECT, false)
    } else {
        name
    }
}

pub(super) fn append_comment(buffer: &mut TextBuffer, comment: &str, indent: i32) {
    buffer
        .append_indent(indent)
        .append("// $VF: ")
        .append(comment)
        .append_line_separator();
}

pub(super) fn error_comment(message: &str) -> impl Iterator<Item = &str> {
    message.split('\n').filter(|line| !line.is_empty())
}
