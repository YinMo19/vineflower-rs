// Copyright 2000-2024 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Infinite, conditional, and counted/enhanced loop statements.

use std::io;

use super::{definitions, invalid, jump_wrapper, required_first, write_label};
use crate::decompiler::exps::{generic_inference::Inference, write};
use crate::decompiler::ir::{ExprId, StatId};
use crate::decompiler::stats::{DoStatement, LoopType};
use crate::engine::Cx;
use crate::util::text_buffer::TextBuffer;

pub(super) fn do_statement(
    cx: &mut Cx,
    stat: StatId,
    loop_: DoStatement,
    indent: i32,
) -> io::Result<TextBuffer> {
    let mut buf = definitions(cx, stat, indent)?;
    write_label(cx, stat, indent, &mut buf);
    let body = required_first(cx, stat)?;

    match loop_.ty {
        LoopType::Infinite => {
            buf.append_indent(indent)
                .append("while (true) {")
                .append_line_separator();
        }
        LoopType::DoWhile => {
            buf.append_indent(indent)
                .append("do {")
                .append_line_separator()
                .append_buffer(&jump_wrapper(cx, body, indent + 1, false)?)
                .append_indent(indent)
                .append("} while (");
            let condition = required_header(loop_.condition(&cx.ir))?;
            append_condition(cx, &mut buf, condition, indent)?;
            buf.append(");").append_line_separator();
            return Ok(buf);
        }
        LoopType::While => {
            buf.append_indent(indent).append("while (");
            let condition = required_header(loop_.condition(&cx.ir))?;
            append_condition(cx, &mut buf, condition, indent)?;
            buf.append(") {").append_line_separator();
        }
        LoopType::For => {
            buf.append_indent(indent)
                .push_newline_group(indent, 1)
                .append("for (");
            if let Some(init) = loop_.init(&cx.ir) {
                buf.append_buffer(&write::to_java(cx, init, indent)?);
            }
            let condition = required_header(loop_.condition(&cx.ir))?;
            buf.append_char(';')
                .append_possible_newline_or(" ", false)
                .append_buffer(&write::to_java(cx, condition, indent)?)
                .append_char(';')
                .append_possible_newline_or(" ", false);
            let increment = required_header(loop_.increment(&cx.ir))?;
            buf.append_buffer(&write::to_java(cx, increment, indent)?)
                .append_possible_newline_or("", true)
                .pop_newline_group();
            buf.append(") {").append_line_separator();
        }
        LoopType::ForEach => {
            let init = required_header(loop_.init(&cx.ir))?;
            buf.append_indent(indent)
                .append("for (")
                .append_buffer(&write::to_java(cx, init, indent)?);
            let iterable = required_header(loop_.increment(&cx.ir))?;
            Inference::for_writing(cx).infer(iterable, None)?;
            buf.append(" : ")
                .append_buffer(&write::to_java(cx, iterable, indent)?)
                .append(") {")
                .append_line_separator();
        }
    }

    buf.append_buffer(&jump_wrapper(
        cx,
        body,
        indent + 1,
        loop_.ty == LoopType::ForEach,
    )?)
    .append_indent(indent)
    .append_char('}')
    .append_line_separator();
    Ok(buf)
}

fn required_header(expr: Option<ExprId>) -> io::Result<ExprId> {
    expr.ok_or_else(|| invalid("Missing loop header expression"))
}

fn append_condition(
    cx: &mut Cx,
    buf: &mut TextBuffer,
    condition: ExprId,
    indent: i32,
) -> io::Result<()> {
    buf.push_newline_group(indent, 1)
        .append_possible_newline()
        .append_buffer(&write::to_java(cx, condition, indent)?)
        .append_possible_newline_or("", true)
        .pop_newline_group();
    Ok(())
}
