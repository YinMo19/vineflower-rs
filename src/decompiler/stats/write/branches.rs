// Copyright 2000-2024 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Source spelling of conditionals and synchronized bodies.

use std::io;

use super::{definitions, invalid, jump_wrapper, required_first, to_java, write_label};
use crate::code::code_constants::OPC_MONITOREXIT;
use crate::decompiler::exps::write;
use crate::decompiler::ir::{ExprListId, StatId};
use crate::decompiler::stats::{IfStatement, StatementKind, stat_edge::EdgeType};
use crate::engine::Cx;
use crate::util::{java_str::utf16_len, text_buffer::TextBuffer};

pub(super) fn if_statement(
    cx: &mut Cx,
    stat: StatId,
    branch: IfStatement,
    indent: i32,
) -> io::Result<TextBuffer> {
    let mut buf = definitions(cx, stat, indent)?;
    let first = required_first(cx, stat)?;
    buf.append_buffer(&to_java(cx, first, indent)?);
    write_label(cx, stat, indent, &mut buf);

    buf.append_indent(indent);
    if let Some(condition) = branch
        .head_exprents
        .and_then(|list| cx.ir[list].first().copied())
    {
        buf.append_buffer(&write::to_java(cx, condition, indent)?);
    } else {
        buf.append("if <null condition>");
    }
    buf.append(" {").append_line_separator();

    if let Some(body) = branch.if_stat {
        buf.append_buffer(&jump_wrapper(cx, body, indent + 1, true)?);
    } else {
        let jump = branch
            .if_edge
            .ok_or_else(|| invalid("Condition has no true edge"))?;
        let jump = &cx.ir[jump];
        if jump.explicit {
            buf.append_indent(indent + 1)
                .append(if jump.edge_type == EdgeType::Break {
                    "break"
                } else {
                    "continue"
                });
            if jump.labeled {
                buf.append(" label");
                match jump.closure {
                    Some(closure) => buf.append_int(cx.ir[closure].id),
                    None => buf.append("<unknownclosure>"),
                };
            }
            buf.append_char(';').append_line_separator();
        }
    }

    if let Some(other) = branch.else_stat {
        if is_else_if(cx, other) {
            buf.append_indent(indent).append("} else ");
            let mut content = jump_wrapper(cx, other, indent, false)?;
            content.set_start(indent.max(0) * utf16_len(&cx.options.indent_string));
            buf.append_buffer(&content);
            return Ok(buf);
        }

        let content = jump_wrapper(cx, other, indent + 1, false)?;
        if content.length() > 0 {
            buf.append_indent(indent)
                .append("} else {")
                .append_line_separator()
                .append_buffer(&content);
        }
    }

    buf.append_indent(indent)
        .append_char('}')
        .append_line_separator();
    Ok(buf)
}

fn is_else_if(cx: &Cx, stat: StatId) -> bool {
    matches!(cx.ir[stat].kind, StatementKind::If(_))
        && cx.ir[stat].var_definitions.is_empty()
        && cx.ir[stat]
            .first
            .and_then(|head| cx.ir[head].exprents)
            .is_some_and(|list| cx.ir[list].is_empty())
        && !stat.is_labeled(&cx.ir)
        && cx.ir[stat]
            .direct_successors()
            .first()
            .is_none_or(|&edge| !cx.ir[edge].explicit)
}

pub(super) fn synchronized(
    cx: &mut Cx,
    stat: StatId,
    body: StatId,
    head_exprents: Option<ExprListId>,
    indent: i32,
) -> io::Result<TextBuffer> {
    let mut buf = definitions(cx, stat, indent)?;
    let first = required_first(cx, stat)?;
    buf.append_buffer(&to_java(cx, first, indent)?);
    write_label(cx, stat, indent, &mut buf);

    buf.append_indent(indent);
    if let Some(head) = head_exprents.and_then(|list| cx.ir[list].first().copied()) {
        buf.append_buffer(&write::to_java(cx, head, indent)?);
    } else {
        buf.append("synchronized <null condition> ");
    }
    buf.append(" {").append_line_separator();

    buf.append_buffer(&jump_wrapper(cx, body, indent + 1, true)?)
        .append_indent(indent)
        .append_char('}');
    let StatementKind::BasicBlock { block } = cx.ir[body.get_basic_head(&cx.ir)].kind else {
        unreachable!()
    };
    let block = &cx.ir[block];
    if block
        .get_last_instruction()
        .is_some_and(|instr| instr.opcode == OPC_MONITOREXIT)
    {
        let offset = block.get_old_offset(block.size() - 1);
        if offset >= 0 {
            buf.add_bytecode_mapping(offset);
        }
    }
    buf.append_line_separator();
    Ok(buf)
}
