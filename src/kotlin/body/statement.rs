// SPDX-License-Identifier: Apache-2.0

//! Kotlin's statement subclasses and KExprProcessor's jump wrapper.

use std::io;

use crate::code::code_constants::OPC_ASTORE;
use crate::decompiler::exps::{Expr, ExprKind, write as expr};
use crate::decompiler::ir::{EdgeId, StatId};
use crate::decompiler::stats::{IfStatement, StatementKind, stat_edge::EdgeType, write as stat};
use crate::engine::Cx;
use crate::types::VarType;
use crate::util::{java_str::utf16_len, text_buffer::TextBuffer};

/// Write a prepared Kotlin body under the owning method's writer context.
/// Inherited statement printers share the Kotlin writer's semicolon policy.
pub fn statement(cx: &mut Cx, root: StatId, indent: i32) -> io::Result<TextBuffer> {
    struct Scope<'a> {
        cx: &'a mut Cx,
        previous: bool,
    }
    impl Drop for Scope<'_> {
        fn drop(&mut self) {
            self.cx.writing_kotlin_body = self.previous;
        }
    }

    let previous = std::mem::replace(&mut cx.writing_kotlin_body, true);
    let scope = Scope { cx, previous };
    stat::to_java(scope.cx, root, indent)
}

pub(crate) fn is_kotlin_statement(cx: &Cx, stat: StatId) -> bool {
    cx.kotlin_body
        .as_ref()
        .is_some_and(|body| body.statements.contains(&stat))
}

pub(crate) fn write_statement(cx: &mut Cx, stat: StatId, indent: i32) -> io::Result<TextBuffer> {
    match cx.ir[stat].kind {
        StatementKind::Sequence => sequence(cx, stat, indent),
        StatementKind::If(branch) => if_statement(cx, stat, indent, branch),
        StatementKind::Catch { .. } => catch(cx, stat, indent),
        StatementKind::Do(loop_) => super::loops::write_loop(cx, stat, indent, loop_),
        StatementKind::Switch(_) => switch(cx, stat, indent),
        _ => unreachable!("Expected a Kotlin statement wrapper"),
    }
}

pub(super) fn jump_wrapper(
    cx: &mut Cx,
    stat: StatId,
    indent: i32,
    in_switch: bool,
) -> io::Result<TextBuffer> {
    let mut result = stat::to_java(cx, stat, indent)?;
    if let &[edge] = cx.ir[stat].direct_successors()
        && cx.ir[edge].edge_type != EdgeType::Regular
        && cx.ir[edge].explicit
        && !matches!(
            cx.ir[cx.ir[edge].destination].kind,
            StatementKind::DummyExit { .. }
        )
    {
        let mut jump = TextBuffer::new(cx);
        jump.append_indent(indent);
        let sequence = is_sequence_closure(cx, edge);
        match cx.ir[edge].edge_type {
            EdgeType::Break => {
                stat::map_deleted_goto(&cx.ir, stat, &mut result);
                if !in_switch || cx.ir[edge].labeled {
                    jump.append(if sequence { "return" } else { "break" });
                }
            }
            EdgeType::Continue => {
                stat::map_deleted_goto(&cx.ir, stat, &mut result);
                jump.append("continue");
            }
            _ => {}
        }
        append_jump_label(cx, edge, sequence, &mut jump)?;
        if !jump.contains_only_whitespaces() {
            result.append_buffer(&jump).append_line_separator();
        }
    }
    Ok(result)
}

fn append_jump_label(
    cx: &Cx,
    edge: EdgeId,
    sequence: bool,
    result: &mut TextBuffer,
) -> io::Result<()> {
    if cx.ir[edge].labeled {
        let label = cx.ir[edge]
            .closure
            .ok_or_else(|| invalid("Kotlin jump label has no closure"))?;
        result.append("@label").append_int(cx.ir[label].id);
    } else if sequence {
        result.append("@run");
    }
    Ok(())
}

fn is_sequence_closure(cx: &Cx, edge: EdgeId) -> bool {
    cx.ir[edge].closure.is_some_and(|closure| {
        is_kotlin_statement(cx, closure) && matches!(cx.ir[closure].kind, StatementKind::Sequence)
    })
}

fn sequence(cx: &mut Cx, stat: StatId, indent: i32) -> io::Result<TextBuffer> {
    let labeled = stat.is_labeled(&cx.ir);
    let mut result = stat::definitions(cx, stat, indent)?;
    let child_indent = indent + i32::from(labeled);
    if labeled {
        result
            .append_indent(indent)
            .append("run label")
            .append_int(cx.ir[stat].id)
            .append("@{")
            .append_line_separator();
    }
    let mut previous_nonempty = false;
    for index in 0..cx.ir[stat].stats.len() {
        let child = cx.ir[stat].stats[index];
        let body = jump_wrapper(cx, child, child_indent, false)?;
        let nonempty = !body.contains_only_whitespaces();
        if index > 0 && nonempty && previous_nonempty {
            result.append_line_separator();
        }
        result.append_buffer(&body);
        previous_nonempty = nonempty;
    }
    if labeled {
        result
            .append_indent(indent)
            .append_char('}')
            .append_line_separator();
    }
    Ok(result)
}

fn if_statement(
    cx: &mut Cx,
    stat: StatId,
    indent: i32,
    branch: IfStatement,
) -> io::Result<TextBuffer> {
    let mut result = stat::definitions(cx, stat, indent)?;
    let first = stat::required_first(cx, stat)?;
    result.append_buffer(&stat::to_java(cx, first, indent)?);
    if stat.is_labeled(&cx.ir) {
        result
            .append_indent(indent)
            .append("label")
            .append_int(cx.ir[stat].id)
            .append_char('@')
            .append_line_separator();
    }
    let head = branch
        .head_exprents
        .and_then(|list| cx.ir[list].first().copied())
        .ok_or_else(|| invalid("Kotlin if statement has no condition"))?;
    result
        .append_indent(indent)
        .append_buffer(&expr::to_java(cx, head, indent)?)
        .append(" {")
        .append_line_separator();
    if let Some(body) = branch.if_stat {
        result.append_buffer(&jump_wrapper(cx, body, indent + 1, false)?);
    } else if let Some(edge) = branch.if_edge.filter(|&edge| cx.ir[edge].explicit) {
        let sequence = is_sequence_closure(cx, edge);
        result
            .append_indent(indent + 1)
            .append(match cx.ir[edge].edge_type {
                EdgeType::Break if sequence => "return",
                EdgeType::Break => "break",
                _ => "continue",
            });
        append_jump_label(cx, edge, sequence, &mut result)?;
        result.append_line_separator();
    }
    if let Some(other) = branch.else_stat {
        let inline = is_kotlin_statement(cx, other)
            && matches!(cx.ir[other].kind, StatementKind::If(_))
            && cx.ir[other].var_definitions.is_empty()
            && cx.ir[other]
                .first
                .and_then(|first| cx.ir[first].exprents)
                .is_some_and(|list| cx.ir[list].is_empty())
            && !other.is_labeled(&cx.ir)
            && cx.ir[other]
                .direct_successors()
                .first()
                .is_none_or(|&edge| !cx.ir[edge].explicit);
        if inline {
            result.append_indent(indent).append("} else ");
            let mut body = jump_wrapper(cx, other, indent, false)?;
            body.set_start(indent_width(cx, indent));
            result.append_buffer(&body);
            return Ok(result);
        }
        let body = jump_wrapper(cx, other, indent + 1, false)?;
        if body.length() > 0 {
            result
                .append_indent(indent)
                .append("} else {")
                .append_line_separator()
                .append_buffer(&body);
        }
    }
    result
        .append_indent(indent)
        .append_char('}')
        .append_line_separator();
    Ok(result)
}

fn catch(cx: &mut Cx, stat: StatId, mut indent: i32) -> io::Result<TextBuffer> {
    let mut result = stat::definitions(cx, stat, indent)?;
    if stat.is_labeled(&cx.ir) {
        result
            .append_indent(indent)
            .append("label")
            .append_int(cx.ir[stat].id)
            .append("@ ");
    }
    result
        .append_indent(indent)
        .append("try {")
        .append_line_separator();
    indent += 1;
    let StatementKind::Catch {
        vars, resources, ..
    } = &cx.ir[stat].kind
    else {
        unreachable!()
    };
    let vars = vars.clone();
    let resources = resources.map_or_else(Vec::new, |list| cx.ir[list].clone());
    for &resource in &resources {
        result.append_int(indent);
        indent += 1;
        result
            .append_buffer(&expr::to_java(cx, resource, indent)?)
            .append(".use {")
            .append_line_separator();
    }
    let first = stat::required_first(cx, stat)?;
    result.append_buffer(&stat::jump_wrapper(cx, first, indent, false)?);
    indent -= 1;
    result.append_indent(indent).append_char('}');
    for _ in resources {
        indent -= 1;
        result
            .append_line_separator()
            .append_indent(indent)
            .append_char('}');
    }
    for (index, var) in vars.into_iter().enumerate() {
        let handler = cx.ir[stat].stats[index + 1];
        let StatementKind::BasicBlock { block } = cx.ir[handler.get_basic_head(&cx.ir)].kind else {
            unreachable!()
        };
        let block = &cx.ir[block];
        if !block.seq.is_empty() && block.get_instruction(0).opcode == OPC_ASTORE {
            let offset = block.get_old_offset(0);
            if offset >= 0 {
                result.add_bytecode_mapping(offset);
            }
        }
        result
            .append(" catch (")
            .append_buffer(&expr::to_java(cx, var, indent)?)
            .append(") {")
            .append_line_separator()
            .append_buffer(&stat::to_java(cx, handler, indent + 1)?)
            .append_indent(indent)
            .append_char('}');
    }
    result.append_line_separator();
    Ok(result)
}

fn switch(cx: &mut Cx, stat: StatId, mut indent: i32) -> io::Result<TextBuffer> {
    let mut result = stat::definitions(cx, stat, indent)?;
    let labeled = stat.is_labeled(&cx.ir);
    if labeled {
        result
            .append_indent(indent)
            .append("run label")
            .append_int(cx.ir[stat].id)
            .append("@{")
            .append_line_separator();
        indent += 1;
    }
    let first = stat::required_first(cx, stat)?;
    let first_body = stat::to_java(cx, first, 0)?;
    result.append_indent(indent).append_buffer(&first_body);
    let phantom = cx.ir[stat].phantom;
    if phantom {
        if !cx.options.show_hidden_statements {
            return Ok(result);
        }
        result
            .append_indent(indent)
            .append("/*")
            .append_line_separator();
    }
    if first_body.length() > 0 {
        result.append_indent(indent);
    }

    let StatementKind::Switch(switch) = &cx.ir[stat].kind else {
        unreachable!()
    };
    let head = switch
        .head_exprents
        .and_then(|list| cx.ir[list].first().copied())
        .ok_or_else(|| invalid("Kotlin switch has no header"))?;
    let default = switch.default_edge;
    let cases = switch.cases.clone();
    result
        .append_buffer(&expr::to_java(cx, head, indent)?)
        .append(" {")
        .append_line_separator();
    let switch_type = Expr::expr_type(cx, head);
    for case in cases {
        let mut any = false;
        for (index, (edge, value)) in case.edges.into_iter().zip(case.values).enumerate() {
            if Some(edge) == default {
                continue;
            }
            any = true;
            let value = value.ok_or_else(|| invalid("Kotlin switch case has no value"))?;
            if index == 0 {
                result.append_indent(indent + 1);
            } else {
                result.append(", ");
            }
            if matches!(&cx.ir[value].kind, ExprKind::Constant { var_type, .. } if *var_type != VarType::VARTYPE_NULL)
            {
                // The plugin allocates and types a copy, then prints the original.
                let cloned = super::copy_ambient(cx, value);
                let ExprKind::Constant { var_type, .. } = &mut cx.ir[cloned].kind else {
                    unreachable!()
                };
                *var_type = switch_type.clone();
            }
            if let ExprKind::Field(field) = &cx.ir[value].kind
                && field.is_static()
                && let Some(owner) = &field.classname
            {
                let (owner, name, desc) =
                    (owner.clone(), field.name.clone(), field.descriptor.clone());
                let short = crate::engine::import_collector::get_short_name(cx, &owner);
                result
                    .append_class(&short, false, &owner)
                    .append_char('.')
                    .append_field_with(&name, false, &owner, &name, desc);
            } else {
                result.append_buffer(&expr::to_java(cx, value, indent)?);
            }
        }
        if any {
            result.append(" -> ");
            write_case(cx, indent + 1, &mut result, case.statement)?;
        }
    }
    if let Some(default) = default {
        result.append_indent(indent + 1).append("else -> ");
        write_case(cx, indent + 1, &mut result, cx.ir[default].destination)?;
    }
    result
        .append_indent(indent)
        .append_char('}')
        .append_line_separator();
    if labeled {
        indent -= 1;
        result
            .append_indent(indent)
            .append_char('}')
            .append_line_separator();
    }
    if phantom {
        result
            .append_indent(indent)
            .append("*/")
            .append_line_separator();
    }
    Ok(result)
}

fn write_case(cx: &mut Cx, indent: i32, result: &mut TextBuffer, stat: StatId) -> io::Result<()> {
    let mut body = jump_wrapper(cx, stat, indent + 1, true)?;
    if body.count_lines() > 1 {
        result
            .append_char('{')
            .append_line_separator()
            .append_buffer(&body)
            .append_indent(indent)
            .append_char('}')
            .append_line_separator();
    } else if !body.contains_only_whitespaces() {
        body.set_start(indent_width(cx, indent + 1));
        result.append_buffer(&body);
    } else {
        result.append("{}").append_line_separator();
    }
    Ok(())
}

fn indent_width(cx: &Cx, indent: i32) -> i32 {
    utf16_len(&cx.options.indent_string) * indent
}

fn invalid(message: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}
