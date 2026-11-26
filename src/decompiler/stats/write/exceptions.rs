// Copyright 2000-2024 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Ordinary and catch-all exception handlers, finally blocks, and resources.

use std::io;

use super::{definitions, invalid, jump_wrapper, list_to_java, required_first, write_label};
use crate::code::code_constants::OPC_ASTORE;
use crate::decompiler::expr_processor::get_cast_type_name;
use crate::decompiler::exps::{ExprKind, write};
use crate::decompiler::ir::{ExprId, StatId};
use crate::decompiler::stats::StatementKind;
use crate::engine::Cx;
use crate::types::VarType;
use crate::util::{java_str::utf16_len, text_buffer::TextBuffer};

pub(super) fn catch(cx: &mut Cx, stat: StatId, indent: i32) -> io::Result<TextBuffer> {
    let mut buf = definitions(cx, stat, indent)?;
    write_label(cx, stat, indent, &mut buf);

    let StatementKind::Catch { resources, .. } = cx.ir[stat].kind else {
        unreachable!()
    };
    let resources = resources.map_or_else(Vec::new, |list| cx.ir[list].clone());
    buf.append_indent(indent);
    match resources.as_slice() {
        [] => buf.append("try {"),
        [resource] => buf
            .append("try (")
            .append_buffer(&write::to_java(cx, *resource, indent + 1)?)
            .append(") {"),
        resources => buf
            .append("try (")
            .append_line_separator()
            .append_buffer(&list_to_java(cx, resources, indent + 1)?)
            .append_indent(indent)
            .append(") {"),
    };
    buf.append_line_separator();
    let first = required_first(cx, stat)?;
    buf.append_buffer(&jump_wrapper(cx, first, indent + 1, true)?)
        .append_indent(indent)
        .append_char('}');

    for index in 1..cx.ir[stat].stats.len() {
        let handler = cx.ir[stat].stats[index];
        let StatementKind::BasicBlock { block } = cx.ir[handler.get_basic_head(&cx.ir)].kind else {
            unreachable!()
        };
        let block = &cx.ir[block];
        if !block.seq.is_empty() && block.get_instruction(0).opcode == OPC_ASTORE {
            let offset = block.get_old_offset(0);
            if offset >= 0 {
                buf.add_bytecode_mapping(offset);
            }
        }

        let StatementKind::Catch {
            ref exceptions,
            ref vars,
            ..
        } = cx.ir[stat].kind
        else {
            unreachable!()
        };
        let types = exceptions[index - 1].clone();
        let var = vars[index - 1];

        buf.append(" catch (");
        for (index, name) in types.into_iter().enumerate() {
            let ty = VarType::from_signature_cl(&name, true);
            let name = get_cast_type_name(cx, &ty);
            if index > 0 {
                buf.append(" | ");
            }
            buf.append(&name);
        }
        buf.append_char(' ')
            .append_buffer(&catch_name(cx, var, indent)?)
            .append(") {")
            .append_line_separator()
            .append_buffer(&jump_wrapper(cx, handler, indent + 1, false)?)
            .append_indent(indent)
            .append_char('}');
    }
    buf.append_line_separator();
    Ok(buf)
}

fn catch_name(cx: &mut Cx, expr: ExprId, indent: i32) -> io::Result<TextBuffer> {
    struct DefinitionScope<'a> {
        cx: &'a mut Cx,
        expr: ExprId,
        previous: bool,
    }
    impl Drop for DefinitionScope<'_> {
        fn drop(&mut self) {
            let ExprKind::Variable(var) = &mut self.cx.ir[self.expr].kind else {
                unreachable!()
            };
            var.definition = self.previous;
        }
    }
    let ExprKind::Variable(var) = &mut cx.ir[expr].kind else {
        return Err(invalid("Catch parameter is not a variable"));
    };
    let previous = std::mem::replace(&mut var.definition, false);
    write::to_java(DefinitionScope { cx, expr, previous }.cx, expr, indent)
}

pub(super) fn catch_all(cx: &mut Cx, stat: StatId, indent: i32) -> io::Result<TextBuffer> {
    let mut buf = definitions(cx, stat, indent)?;
    write_label(cx, stat, indent, &mut buf);

    let StatementKind::CatchAll {
        handler,
        is_finally,
        monitor,
        ref vars,
    } = cx.ir[stat].kind
    else {
        unreachable!()
    };
    let var = vars.first().copied();
    let first = required_first(cx, stat)?;
    if matches!(cx.ir[first].kind, StatementKind::Catch { .. })
        && cx.ir[first].var_definitions.is_empty()
        && is_finally
        && !stat.is_labeled(&cx.ir)
        && !first.is_labeled(&cx.ir)
        && cx.ir[first]
            .direct_successors()
            .first()
            .is_none_or(|&edge| !cx.ir[edge].explicit)
    {
        let mut content = jump_wrapper(cx, first, indent, true)?;
        content.set_length(content.length() - utf16_len(cx.options.line_separator()));
        buf.append_buffer(&content);
    } else {
        buf.append_indent(indent)
            .append("try {")
            .append_line_separator()
            .append_buffer(&jump_wrapper(cx, first, indent + 1, true)?)
            .append_indent(indent)
            .append_char('}');
    }

    if is_finally {
        buf.append(" finally");
    } else {
        let var = var.ok_or_else(|| invalid("Catch-all has no exception variable"))?;
        buf.append(" catch (")
            .append_buffer(&write::to_java(cx, var, indent)?)
            .append_char(')');
    }
    buf.append(" {").append_line_separator();

    if let Some(monitor) = monitor {
        buf.append_indent(indent + 1)
            .append("if (")
            .append_buffer(&write::to_java(cx, monitor, indent)?)
            .append(") {")
            .append_line_separator();
    }
    let handler = handler.ok_or_else(|| invalid("Catch-all has no handler"))?;
    buf.append_buffer(&jump_wrapper(
        cx,
        handler,
        indent + 1 + i32::from(monitor.is_some()),
        true,
    )?);
    if monitor.is_some() {
        buf.append_indent(indent + 1)
            .append_char('}')
            .append_line_separator();
    }
    buf.append_indent(indent)
        .append_char('}')
        .append_line_separator();
    Ok(buf)
}
