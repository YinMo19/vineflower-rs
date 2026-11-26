// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! ClassWriter.writeClass renders members into separate buffers so their
//! bytecode ranges and skipped declarations agree with the final layout.

use super::{declaration, fields, methods};
use crate::code::code_constants::*;
use crate::engine::{
    Cx,
    class_nodes::{ClassKind, ClassNodeId},
    class_wrapper::catch_method_failure,
};
use crate::structs::{StructClass, StructMember, StructMethod};
use crate::util::{interpreter_util::make_unique_key, text_buffer::TextBuffer};
use std::{io, sync::Arc};

pub fn write_class(
    cx: &mut Cx,
    node: ClassNodeId,
    buffer: &mut TextBuffer,
    indent: i32,
) -> io::Result<()> {
    cx.with_class_node(node, |cx| {
        if cx.class_nodes[node].wrapper.is_none() {
            buffer
                .append("/* $VF: Couldn't be decompiled. Class ")
                .append(&cx.class_nodes[node].class.qualified_name)
                .append(" wasn't processed yet! */");
            error_comments(cx, buffer);
            return Ok(());
        }
        if let Err(error) = catch_method_failure(|| super::prepare(cx, node)) {
            if error.kind() == io::ErrorKind::Interrupted {
                return Err(error);
            }
            log::warn!(
                "Class {:?} couldn't be written: {error}",
                cx.class_nodes[node].simple_name
            );
            super::method_errors::write_exception(cx, buffer, &error);
            return Ok(());
        }
        let class = Arc::clone(&cx.class_nodes[node].class);
        if cx.options.sourcefile_comments
            && let Some(attr) = &class.attributes.source_file
        {
            buffer
                .append_indent(indent)
                .append("// $VF: Compiled from ")
                .append(&attr.get_source_file(&class.pool))
                .append_line_separator();
        }
        declaration::append_definition(cx, node, buffer, indent)?;
        let anonymous = cx.class_nodes[node].kind == ClassKind::Anonymous;
        let mut body = Body {
            buffer,
            anonymous,
            has_content: false,
        };
        if cx.options.method_to_decompile.is_empty() {
            write_fields(cx, node, &class, &mut body, indent + 1)?;
        }
        for (index, method) in class.methods.iter().enumerate() {
            if !include_method(cx, node, method) {
                continue;
            }
            let mut method_buffer = TextBuffer::new(cx);
            if methods::write_method(cx, node, index, &mut method_buffer, indent + 1)? {
                body.separate_member();
                body.begin_content().append_buffer(&method_buffer);
            }
        }
        for child in cx.class_nodes[node].nested.clone() {
            if !include_member_class(cx, node, child) {
                continue;
            }
            body.separate_member();
            let mut inner = TextBuffer::new(cx);
            write_class(cx, child, &mut inner, indent + 1)?;
            body.begin_content().append_buffer(&inner);
        }
        if body.has_content || !anonymous {
            body.buffer.append_indent(indent);
        }
        body.buffer.append_char('}');
        if !anonymous {
            body.buffer.append_line_separator();
        }
        Ok(())
    })
}

struct Body<'a> {
    buffer: &'a mut TextBuffer,
    anonymous: bool,
    has_content: bool,
}

impl Body<'_> {
    fn separate_member(&mut self) {
        if self.has_content {
            self.buffer.append_line_separator();
        }
    }
    fn begin_content(&mut self) -> &mut TextBuffer {
        if self.anonymous && !self.has_content {
            self.buffer.append_line_separator();
        }
        self.has_content = true;
        self.buffer
    }
}

fn write_fields(
    cx: &mut Cx,
    node: ClassNodeId,
    class: &StructClass,
    body: &mut Body<'_>,
    indent: i32,
) -> io::Result<()> {
    let (enums, ordinary): (Vec<_>, Vec<_>) = class
        .fields
        .iter()
        .partition(|f| cx.options.decompile_enums && f.has_modifier(ACC_ENUM));
    let mut after_enums = !enums.is_empty();
    let field_buffer =
        |cx: &mut Cx, fd: &crate::structs::StructField, buf: &mut TextBuffer| -> io::Result<()> {
            let mut field = TextBuffer::new(cx);
            fields::write_field(cx, node, fd, &mut field, indent)?;
            let method = if fd.has_modifier(ACC_STATIC) {
                "<clinit> ()V"
            } else {
                "<init> ()V"
            };
            buf.append_buffer_for(&field, Some(&class.qualified_name), Some(method));
            Ok(())
        };
    for (index, fd) in enums.into_iter().enumerate() {
        if index > 0 {
            body.buffer.append_char(',').append_line_separator();
        }
        field_buffer(cx, fd, body.begin_content())?;
    }
    if after_enums {
        body.buffer.append_char(';').append_line_separator();
    }
    for fd in ordinary {
        if cx.options.remove_synthetic && fd.is_synthetic()
            || cx.class_nodes[node]
                .hidden_members
                .contains(&make_unique_key(&fd.name, &fd.descriptor))
        {
            continue;
        }
        if fd.access_flags == (ACC_FINAL | ACC_PRIVATE)
            && class.get_record_components().is_some_and(|cs| {
                cs.iter()
                    .any(|c| c.name == fd.name && c.descriptor == fd.descriptor)
            })
        {
            continue;
        }
        if after_enums {
            body.buffer.append_line_separator();
            after_enums = false;
        }
        field_buffer(cx, fd, body.begin_content())?;
    }
    Ok(())
}

fn include_method(cx: &Cx, node: ClassNodeId, method: &StructMethod) -> bool {
    let node = &cx.class_nodes[node];
    let selection = &cx.options.method_to_decompile;
    if selection.is_empty() || !matches!(node.kind, ClassKind::Root | ClassKind::Member) {
        return !(cx.options.remove_synthetic && method.is_synthetic()
            || cx.options.remove_bridge && method.has_modifier(ACC_BRIDGE)
            || node
                .hidden_members
                .contains(&make_unique_key(&method.name, &method.descriptor)));
    }
    let key = format!("{}{}", method.name, method.descriptor);
    (node.kind == ClassKind::Root && *selection == key)
        || selection
            .strip_prefix(node.class.qualified_name.as_str())
            .and_then(|s| s.strip_prefix('.'))
            == Some(&key)
}

fn include_member_class(cx: &Cx, node: ClassNodeId, child: ClassNodeId) -> bool {
    let child = &cx.class_nodes[child];
    if child.kind != ClassKind::Member {
        return false;
    }
    let name = &child.class.qualified_name;
    if cx.options.method_to_decompile.is_empty() {
        let synthetic = child.access & ACC_SYNTHETIC != 0 || child.class.is_synthetic();
        !(synthetic && cx.options.remove_synthetic
            || cx.class_nodes[node].hidden_members.contains(name.as_str()))
    } else {
        cx.options
            .method_to_decompile
            .strip_prefix(name.as_str())
            .is_some_and(|suffix| suffix.starts_with('.'))
    }
}

fn error_comments(cx: &Cx, buffer: &mut TextBuffer) {
    for line in cx
        .options
        .error_message
        .split('\n')
        .filter(|line| !line.is_empty())
    {
        buffer.append("// ").append(line).append_line_separator();
    }
}
