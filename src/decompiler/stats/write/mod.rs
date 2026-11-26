// Copyright 2000-2024 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Write the structured statement tree while retaining expression buffers and mappings.

mod branches;
mod exceptions;
mod loops;
mod switches;

pub(crate) use switches::switch_expression;

use std::io;

use super::{StatementKind, stat_edge::EdgeType};
use crate::decompiler::exps::{Expr, ExprKind, MonitorType, generic_inference::Inference, write};
use crate::decompiler::ir::{ExprId, Ir, StatId};
use crate::engine::Cx;
use crate::util::text_buffer::TextBuffer;

/// `Statement.toJava`. The caller selects the owning method and attaches
/// its dummy-exit offsets when writing the complete method body.
pub fn to_java(cx: &mut Cx, stat: StatId, indent: i32) -> io::Result<TextBuffer> {
    if crate::kotlin::body::is_kotlin_statement(cx, stat) {
        return crate::kotlin::body::write_statement(cx, stat, indent);
    }
    match cx.ir[stat].kind {
        StatementKind::BasicBlock { .. } => basic_block(cx, stat, indent),
        StatementKind::General { .. } => general(cx, stat, indent),
        StatementKind::Do(loop_) => loops::do_statement(cx, stat, loop_, indent),
        StatementKind::Switch(_) => switches::statement(cx, stat, indent),
        StatementKind::If(branch) => branches::if_statement(cx, stat, branch, indent),
        StatementKind::Sequence => sequence(cx, stat, indent),
        StatementKind::Catch { .. } => exceptions::catch(cx, stat, indent),
        StatementKind::CatchAll { .. } => exceptions::catch_all(cx, stat, indent),
        StatementKind::Synchronized {
            body,
            head_exprents,
        } => branches::synchronized(cx, stat, body, head_exprents, indent),
        StatementKind::Root { .. } => {
            let mut buf = definitions(cx, stat, indent)?;
            let first = required_first(cx, stat)?;
            buf.append_buffer(&to_java(cx, first, indent)?);
            Ok(buf)
        }
        StatementKind::DummyExit { .. } => Err(invalid("Dummy exit has no source statement")),
    }
}

pub(crate) fn definitions(cx: &mut Cx, stat: StatId, indent: i32) -> io::Result<TextBuffer> {
    let definitions = cx.ir[stat].var_definitions.clone();
    list_to_java(cx, &definitions, indent)
}

/// `ExprProcessor.listToJava`, with variable definitions ordered within each
/// contiguous run as in `Exprent.sortIndexed`.
pub(super) fn list_to_java(cx: &mut Cx, exprs: &[ExprId], indent: i32) -> io::Result<TextBuffer> {
    let mut ordered = exprs.to_vec();
    let definition_index = |expr| {
        Expr::variable(&cx.ir, expr)
            .filter(|var| var.definition)
            .map(|var| var.index)
    };
    for run in ordered
        .chunk_by_mut(|&a, &b| definition_index(a).is_some() && definition_index(b).is_some())
    {
        if run.len() > 1 {
            run.sort_by_key(|&expr| definition_index(expr));
        }
    }

    let mut buf = TextBuffer::new(cx);
    for expr in ordered {
        let local_class = Expr::variable(&cx.ir, expr).is_some_and(|var| var.class_definition);
        if local_class && buf.length() > 0 {
            buf.append_line_separator();
        }

        Inference::for_writing(cx).infer(expr, None)?;
        let content = write::to_java(cx, expr, indent)?;
        if content.length() == 0 {
            continue;
        }
        if !local_class {
            buf.append_indent(indent);
        }
        buf.append_buffer(&content);
        if matches!(
            cx.ir[expr].kind,
            ExprKind::Monitor {
                kind: MonitorType::Enter,
                ..
            }
        ) {
            buf.append("{} // $VF: monitorenter ");
        }
        if !cx.writing_kotlin_body
            && !local_class
            && !matches!(
                cx.ir[expr].kind,
                ExprKind::SwitchHead { .. } | ExprKind::Monitor { .. } | ExprKind::If { .. }
            )
        {
            buf.append_char(';');
        }
        buf.append_line_separator();
    }
    Ok(buf)
}

/// `ExprProcessor.jmpWrapper` prints the sole explicit outgoing jump. Empty
/// bodies receive a semicolon only in the contexts that request one.
pub(crate) fn jump_wrapper(
    cx: &mut Cx,
    stat: StatId,
    indent: i32,
    semicolon_if_empty: bool,
) -> io::Result<TextBuffer> {
    let mut buf = to_java(cx, stat, indent)?;
    if let &[edge] = cx.ir[stat].direct_successors() {
        let edge = &cx.ir[edge];
        if edge.edge_type != EdgeType::Regular
            && edge.explicit
            && !matches!(
                cx.ir[edge.destination].kind,
                StatementKind::DummyExit { .. }
            )
        {
            buf.append_indent(indent);
            match edge.edge_type {
                EdgeType::Break | EdgeType::Continue => {
                    map_deleted_goto(&cx.ir, stat, &mut buf);
                    buf.append(if edge.edge_type == EdgeType::Break {
                        "break"
                    } else {
                        "continue"
                    });
                }
                _ => {}
            }
            if edge.labeled {
                let closure = edge
                    .closure
                    .ok_or_else(|| invalid("Labeled jump has no closure"))?;
                buf.append(" label").append_int(cx.ir[closure].id);
            }
            buf.append_char(';').append_line_separator();
        }
    }
    if buf.length() == 0 && semicolon_if_empty {
        buf.append_indent(indent)
            .append_char(';')
            .append_line_separator();
    }
    Ok(buf)
}

pub(super) fn write_label(cx: &Cx, stat: StatId, indent: i32, buffer: &mut TextBuffer) {
    if stat.is_labeled(&cx.ir) {
        append_label(buffer, indent, cx.ir[stat].id, "");
    }
}

fn append_label(buffer: &mut TextBuffer, indent: i32, id: i32, suffix: &str) {
    buffer
        .append_indent(indent)
        .append("label")
        .append_int(id)
        .append_char(':')
        .append(suffix)
        .append_line_separator();
}

pub(crate) fn map_deleted_goto(ir: &Ir, stat: StatId, buf: &mut TextBuffer) {
    if let StatementKind::BasicBlock { block } = ir[stat].kind
        && ir[block].instr_old_offsets.len() > ir[block].size() as usize
    {
        buf.add_bytecode_mapping(*ir[block].instr_old_offsets.last().unwrap());
    }
}

fn basic_block(cx: &mut Cx, stat: StatId, indent: i32) -> io::Result<TextBuffer> {
    let mut buf = definitions(cx, stat, indent)?;
    if stat.is_labeled(&cx.ir) {
        append_label(&mut buf, indent, cx.ir[stat].id, "// $VF: Invalid label!");
    }
    if let Some(expressions) = cx.ir[stat].exprents {
        let expressions = cx.ir[expressions].clone();
        buf.append_buffer(&list_to_java(cx, &expressions, indent)?);
    }
    Ok(buf)
}

fn general(cx: &mut Cx, stat: StatId, indent: i32) -> io::Result<TextBuffer> {
    let mut buf = TextBuffer::new(cx);
    write_label(cx, stat, indent, &mut buf);
    buf.append_indent(indent)
        .append("abstract statement {")
        .append_line_separator();
    for i in 0..cx.ir[stat].stats.len() {
        let child = cx.ir[stat].stats[i];
        buf.append_buffer(&to_java(cx, child, indent + 1)?);
    }
    buf.append_indent(indent)
        .append_char('}')
        .append_line_separator();
    Ok(buf)
}

fn sequence(cx: &mut Cx, stat: StatId, indent: i32) -> io::Result<TextBuffer> {
    let mut buf = definitions(cx, stat, indent)?;
    let labeled = stat.is_labeled(&cx.ir);
    let child_indent = indent + i32::from(labeled);
    if labeled {
        append_label(&mut buf, indent, cx.ir[stat].id, " {");
    }

    let mut previous_nonempty = false;
    for i in 0..cx.ir[stat].stats.len() {
        let child = cx.ir[stat].stats[i];
        let content = jump_wrapper(cx, child, child_indent, false)?;
        let nonempty = !content.contains_only_whitespaces();
        if i > 0 && previous_nonempty && nonempty {
            buf.append_line_separator();
        }
        buf.append_buffer(&content);
        previous_nonempty = nonempty;
    }

    if labeled {
        buf.append_indent(indent)
            .append_char('}')
            .append_line_separator();
    }
    Ok(buf)
}

pub(crate) fn required_first(cx: &Cx, stat: StatId) -> io::Result<StatId> {
    cx.ir[stat]
        .first
        .ok_or_else(|| invalid("Statement has no first child"))
}

fn invalid(message: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}
