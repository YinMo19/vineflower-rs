// SPDX-License-Identifier: Apache-2.0

//! KDoStatement's loop printers and range recovery at the source boundary.

use std::io;

use crate::decompiler::exps::{Expr, ExprKind, FunctionType, generic_inference::Inference, write};
use crate::decompiler::ir::{ExprId, StatId};
use crate::decompiler::stats::{DoStatement, LoopType, write as statements};
use crate::engine::Cx;
use crate::structs::consts::ConstantValue;
use crate::types::CodeType;
use crate::util::text_buffer::TextBuffer;

use super::statement::jump_wrapper;
use super::{
    Declaration, KotlinExpr, ambient_counters, expression::variable_name, passes,
    replace_expression,
};

pub(super) fn write_loop(
    cx: &mut Cx,
    stat: StatId,
    indent: i32,
    loop_: DoStatement,
) -> io::Result<TextBuffer> {
    if loop_.ty == LoopType::For {
        return counted_loop(cx, stat, indent, loop_);
    }
    let mut result = statements::definitions(cx, stat, indent)?;
    result.append_indent(indent);
    if stat.is_labeled(&cx.ir) {
        label(cx, stat, &mut result).append("@ ");
    }
    let body = statements::required_first(cx, stat)?;
    match loop_.ty {
        LoopType::Infinite => {
            result.append("while (true) {").append_line_separator();
        }
        LoopType::While | LoopType::DoWhile => {
            let cond = required(loop_.condition(&cx.ir), "Kotlin loop has no condition")?;
            let cond = replace_expression(cx, cond)?;
            if loop_.ty == LoopType::DoWhile {
                result
                    .append("do {")
                    .append_line_separator()
                    .append_buffer(&jump_wrapper(cx, body, indent + 1, false)?)
                    .append_indent(indent)
                    .append("} ");
            }
            result
                .append("while (")
                .push_newline_group(indent, 1)
                .append_possible_newline()
                .append_buffer(&write::to_java(cx, cond, indent)?)
                .append_possible_newline_or("", true);
            result.pop_newline_group();
            if loop_.ty == LoopType::DoWhile {
                result.append_char(')').append_line_separator();
                return Ok(result);
            }
            result.append(") {").append_line_separator();
        }
        LoopType::ForEach => {
            let init = required(loop_.init(&cx.ir), "Kotlin foreach loop has no variable")?;
            let mut counters = ambient_counters(cx);
            let init =
                passes::wrap_variable(cx, &mut counters, init, Some(Declaration::ForLoopVariable));
            let inc = required(
                loop_.increment(&cx.ir),
                "Kotlin foreach loop has no iterable",
            )?;
            let inc = replace_expression(cx, inc)?;
            result
                .append("for (")
                .append_buffer(&write::to_java(cx, init, indent)?);
            Inference::for_writing(cx).infer(inc, None)?;
            result
                .append(" in ")
                .append_buffer(&write::to_java(cx, inc, indent)?)
                .append(") {")
                .append_line_separator();
        }
        LoopType::For => unreachable!(),
    }
    result
        .append_buffer(&jump_wrapper(cx, body, indent + 1, false)?)
        .append_indent(indent)
        .append_char('}')
        .append_line_separator();
    Ok(result)
}

fn counted_loop(
    cx: &mut Cx,
    stat: StatId,
    mut indent: i32,
    loop_: DoStatement,
) -> io::Result<TextBuffer> {
    let labeled = stat.is_labeled(&cx.ir);
    let body = statements::required_first(cx, stat)?;
    let mut result = TextBuffer::new(cx);
    result.append_indent(indent);

    match classify_counted_loop(cx, loop_) {
        CountedLoop::UnresolvedBound => return Ok(result),
        CountedLoop::General => {}
        CountedLoop::Range(range) => {
            if range.ascending && is_zero(cx, range.start) {
                result
                    .append("repeat(")
                    .append_buffer(&write::to_java(cx, range.end, 0)?)
                    .append(") ");
                if labeled {
                    label(cx, stat, &mut result).append_char('@');
                }
                result.append_char('{');
                let var = Expr::variable(&cx.ir, range.variable).expect("Kotlin range variable");
                if variable_name(cx, var) != "it" {
                    result
                        .append_char(' ')
                        .append_buffer(&write::to_java(cx, range.variable, indent)?)
                        .append(" ->");
                }
                result.append_line_separator();
            } else {
                if labeled {
                    label(cx, stat, &mut result).append("@ ");
                }
                result
                    .append("for (")
                    .append_buffer(&write::to_java(cx, range.variable, indent)?)
                    .append(" in ")
                    .append_buffer(&write::to_java(cx, range.start, 0)?)
                    .append(if range.ascending { ".." } else { " downTo " })
                    .append_buffer(&write::to_java(cx, range.end, 0)?)
                    .append(") {")
                    .append_line_separator();
            }
            result
                .append_buffer(&jump_wrapper(cx, body, indent + 1, false)?)
                .append_indent(indent)
                .append_char('}')
                .append_line_separator();
            return Ok(result);
        }
    }

    let init = loop_
        .init(&cx.ir)
        .map(|init| replace_expression(cx, init))
        .transpose()?;
    let condition = required(loop_.condition(&cx.ir), "Kotlin for loop has no condition")?;
    let condition = replace_expression(cx, condition)?;
    let increment = required(loop_.increment(&cx.ir), "Kotlin for loop has no increment")?;
    let increment = replace_expression(cx, increment)?;
    result
        .append("// $VF: Unable to resugar Kotlin loop from Java for loop")
        .append_line_separator()
        .append_indent(indent);
    if labeled {
        label_run(cx, stat, &mut result);
        indent += 1;
        result.append_indent(indent);
    }
    if let Some(init) = init {
        result
            .append_buffer(&write::to_java(cx, init, indent)?)
            .append_line_separator()
            .append_indent(indent);
    }
    result
        .append("while (true) {")
        .append_line_separator()
        .append_indent(indent + 1)
        .append("if (")
        .append_buffer(&write::to_java(cx, condition, indent + 1)?)
        .append(") break")
        .append_line_separator()
        .append_buffer(&jump_wrapper(cx, body, indent + 1, false)?)
        .append_line_separator()
        .append_indent(indent + 1)
        .append_buffer(&write::to_java(cx, increment, indent + 1)?)
        .append_line_separator()
        .append_indent(indent)
        .append_char('}')
        .append_line_separator();
    if labeled {
        result
            .append_indent(indent - 1)
            .append_char('}')
            .append_line_separator();
    }
    Ok(result)
}

struct Range {
    variable: ExprId,
    start: ExprId,
    end: ExprId,
    ascending: bool,
}

enum CountedLoop {
    General,
    Range(Range),
    /// KDoStatement breaks out of its labeled resugar block after matching
    /// the loop header if neither operand supplies a supported range bound.
    UnresolvedBound,
}

fn classify_counted_loop(cx: &mut Cx, loop_: DoStatement) -> CountedLoop {
    use FunctionType::*;
    let Some(init) = loop_.init(&cx.ir) else {
        return CountedLoop::General;
    };
    let ExprKind::Assignment {
        left: variable,
        right: start,
        ..
    } = cx.ir[init].kind
    else {
        return CountedLoop::General;
    };
    let ty = Expr::expr_type(cx, variable);
    if Expr::variable(&cx.ir, variable).is_none()
        || (ty.array_dim != 0
            || !matches!(
                ty.ty,
                CodeType::Int | CodeType::Byte | CodeType::Short | CodeType::Char | CodeType::Long
            ))
    {
        return CountedLoop::General;
    }
    let Some(increment) = loop_.increment(&cx.ir) else {
        return CountedLoop::General;
    };
    let ExprKind::Function { op, .. } = cx.ir[increment].kind else {
        return CountedLoop::General;
    };
    if !op.is_inc_dec() {
        return CountedLoop::General;
    }
    let Some(condition) = loop_.condition(&cx.ir) else {
        return CountedLoop::General;
    };
    let ExprKind::Function {
        op: Lt, operands, ..
    } = &cx.ir[condition].kind
    else {
        return CountedLoop::General;
    };
    let (lhs, rhs) = (operands[0], operands[1]);
    let mut counters = ambient_counters(cx);
    let variable = passes::wrap_variable(
        cx,
        &mut counters,
        variable,
        Some(Declaration::ForLoopVariable),
    );
    let ascending = matches!(op, Ipp | Ppi);
    let bound = [rhs, lhs]
        .into_iter()
        .find(|&expr| matches!(cx.ir[expr].kind, ExprKind::Constant { .. }));
    let end = if let Some(bound) = bound {
        let ExprKind::Constant {
            value,
            bool_permitted,
            ..
        } = &cx.ir[bound].kind
        else {
            unreachable!()
        };
        let offsets = cx.ir[bound].bytecode.clone();
        let end = Expr::new_ambient(
            cx,
            ExprKind::Constant {
                value: value.clone(),
                var_type: ty.clone(),
                bool_permitted: *bool_permitted,
                was_condy: false,
            },
            offsets.clone(),
        );
        cx.set_kotlin_expr(end, KotlinExpr::Constant { unsigned: None });
        if let ExprKind::Constant {
            value: ConstantValue::Integer(value),
            ..
        } = cx.ir[end].kind
        {
            let adjusted = value.wrapping_add(if ascending { -1 } else { 1 });
            let kind = Expr::constant(ty.clone(), ConstantValue::Integer(adjusted), false);
            Expr::new_ambient(cx, kind.clone(), offsets.clone());
            let end = Expr::new_ambient(cx, kind, offsets);
            cx.set_kotlin_expr(end, KotlinExpr::Constant { unsigned: None });
            end
        } else {
            end
        }
    } else if Expr::equals(cx, variable, lhs) && Expr::variable(&cx.ir, rhs).is_some() {
        passes::wrap_variable(cx, &mut counters, rhs, None)
    } else if Expr::equals(cx, variable, rhs) && Expr::variable(&cx.ir, lhs).is_some() {
        passes::wrap_variable(cx, &mut counters, lhs, None)
    } else {
        return CountedLoop::UnresolvedBound;
    };
    if let ExprKind::Constant { var_type, .. } = &mut cx.ir[start].kind {
        *var_type = ty;
    }
    CountedLoop::Range(Range {
        variable,
        start,
        end,
        ascending,
    })
}

fn is_zero(cx: &Cx, expr: ExprId) -> bool {
    matches!(
        cx.ir[expr].kind,
        ExprKind::Constant {
            value: ConstantValue::Integer(0),
            ..
        }
    )
}

fn label<'a>(cx: &Cx, stat: StatId, result: &'a mut TextBuffer) -> &'a mut TextBuffer {
    result.append("label").append_int(cx.ir[stat].id)
}

fn label_run(cx: &Cx, stat: StatId, result: &mut TextBuffer) {
    result.append("run ");
    label(cx, stat, result).append("@{").append_line_separator();
}

fn required(expr: Option<ExprId>, message: &'static str) -> io::Result<ExprId> {
    expr.ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, message))
}
