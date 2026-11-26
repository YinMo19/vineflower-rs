// Copyright 2000-2024 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Switch statement and switch expression rendering.

use std::io;

use rustc_hash::FxHashSet;

use super::{definitions, invalid, jump_wrapper, required_first, to_java, write_label};
use crate::code::code_constants::ACC_ENUM;
use crate::decompiler::exps::{
    ConstantValue, ExitType, Expr, ExprKind, FunctionType, WriteFlags, write,
};
use crate::decompiler::ir::{EdgeId, ExprId, Ir, StatId};
use crate::decompiler::stats::{StatementKind, SwitchStatement, stat_edge::EdgeType};
use crate::engine::{Cx, counter_container::CounterContainer};
use crate::types::VarType;
use crate::util::text_buffer::TextBuffer;

pub(super) fn statement(cx: &mut Cx, stat: StatId, indent: i32) -> io::Result<TextBuffer> {
    let mut buf = definitions(cx, stat, indent)?;
    let first = required_first(cx, stat)?;
    buf.append_buffer(&to_java(cx, first, indent)?);

    let phantom = cx.ir[stat].phantom;
    if phantom && !cx.options.show_hidden_statements {
        return Ok(buf);
    }
    write_label(cx, stat, indent, &mut buf);
    buf.append_indent(indent);
    if phantom {
        buf.append("/*");
    }

    let head = head_expression(&cx.ir, stat)?;
    buf.append_buffer(&write::to_java(cx, head, indent)?)
        .append(" {")
        .append_line_separator();
    let switch_type = Expr::expr_type(cx, head);

    for index in 0..switch(&cx.ir, stat).cases.len() {
        let table = switch(&cx.ir, stat);
        let case = &table.cases[index];
        let body = case.statement;
        let scoped = table.scoped_case_statements.contains(&body);
        let guard = table.case_guards.get(index).copied().flatten();
        let default = table.default_edge;
        let edge_count = case.edges.len();

        for label in 0..edge_count {
            let case = &switch(&cx.ir, stat).cases[index];
            buf.append_indent(indent + 1);
            if Some(case.edges[label]) == default {
                buf.append("default");
            } else {
                let value = case
                    .values
                    .get(label)
                    .copied()
                    .flatten()
                    .ok_or_else(|| invalid("Switch case has no value"))?;
                buf.append("case ");
                write_case_value(cx, value, Some(&switch_type), indent, &mut buf)?;
                write_guard(cx, guard, &mut buf)?;
            }
            buf.append_char(':');
            if scoped && label + 1 == edge_count {
                buf.append(" {");
            }
            buf.append_line_separator();
        }

        buf.append_buffer(&jump_wrapper(cx, body, indent + 2, false)?);
        if scoped {
            buf.append_indent(indent + 1)
                .append_char('}')
                .append_line_separator();
        }
    }

    buf.append_indent(indent)
        .append_char('}')
        .append_line_separator();
    if phantom {
        buf.append("*/");
    }
    Ok(buf)
}

pub(crate) fn switch_expression(cx: &mut Cx, expr: ExprId, indent: i32) -> io::Result<TextBuffer> {
    let ExprKind::Switch {
        backing,
        ref var_type,
        standalone,
        ..
    } = cx.ir[expr].kind
    else {
        return Err(invalid("Expected a switch expression"));
    };
    if !cx.ir[backing].phantom {
        return Err(invalid(
            "Switch expression backing statement isn't phantom!",
        ));
    }
    let result_type = var_type.clone();

    let head = head_expression(&cx.ir, backing)?;
    let switch_type = Expr::expr_type(cx, head);
    let exhaustive = is_exhaustive(cx, backing, &switch_type);
    let label_type = (!standalone).then_some(&switch_type);

    let mut buf = TextBuffer::new(cx);
    buf.append_buffer(&write::to_java(cx, head, indent)?)
        .append(" {")
        .append_line_separator();
    for index in 0..switch(&cx.ir, backing).cases.len() {
        let table = switch(&cx.ir, backing);
        let case = &table.cases[index];
        let body = case.statement;
        let guard = table.case_guards.get(index).copied().flatten();
        let default = table.default_edge;
        let edge_count = case.edges.len();
        let has_default = if let Some(edge) = default.filter(|edge| case.edges.contains(edge)) {
            !exhaustive || !is_synthetic_throw_edge(cx, edge)?
        } else {
            false
        };

        let mut has_label = false;
        for label in 0..edge_count {
            let case = &switch(&cx.ir, backing).cases[index];
            let value = if Some(case.edges[label]) == default && case.values.len() <= label {
                // A total pattern in Java 17 also matches null.
                Some(Expr::new_ambient(
                    cx,
                    Expr::constant(VarType::VARTYPE_NULL, ConstantValue::Null, false),
                    None,
                ))
            } else {
                *case
                    .values
                    .get(label)
                    .ok_or_else(|| invalid("Switch expression case is missing a value slot"))?
            };
            let Some(value) = value else {
                continue;
            };
            // A tableswitch can have holes targeting default. Only a null
            // label changes the meaning of a shared default arm.
            if has_default && Expr::expr_type(cx, value) != VarType::VARTYPE_NULL {
                continue;
            }
            if has_label {
                buf.append(", ");
            } else {
                buf.append_indent(indent + 1).append("case ");
            }
            write_case_value(cx, value, label_type, indent, &mut buf)?;
            has_label = true;
        }

        write_guard(cx, guard, &mut buf)?;
        if has_default {
            if has_label {
                buf.append(", default");
            } else {
                if is_empty_default(&cx.ir, body) {
                    continue;
                }
                buf.append_indent(indent + 1).append("default");
            }
            has_label = true;
        }
        if has_label {
            buf.append(" -> ");
            write_expression_arm(cx, body, &result_type, indent, &mut buf)?;
            buf.append_line_separator();
        }
    }

    buf.append_indent(indent).append_char('}');
    Ok(buf)
}

fn write_case_value(
    cx: &mut Cx,
    mut value: ExprId,
    label_type: Option<&VarType>,
    indent: i32,
    buf: &mut TextBuffer,
) -> io::Result<()> {
    if let Some(ty) = label_type
        && matches!(&cx.ir[value].kind, ExprKind::Constant { var_type, .. } if *var_type != VarType::VARTYPE_NULL)
    {
        let mut counters = CounterContainer::with_expression_ids(cx.expression_ids.clone());
        value = Expr::copy(cx, &mut counters, value);
        set_constant_type(&mut cx.ir, value, ty);
    }

    match &cx.ir[value].kind {
        ExprKind::Field(field) if field.is_static() => {
            let owner = field
                .classname
                .as_deref()
                .ok_or_else(|| invalid("Static switch case has no field owner"))?;
            buf.append_field_with(
                &field.name,
                false,
                owner,
                &field.name,
                field.descriptor.clone(),
            );
            return Ok(());
        }
        ExprKind::Function {
            op: FunctionType::InstanceOf,
            operands,
            ..
        } => {
            value = *operands
                .get(2)
                .ok_or_else(|| invalid("Pattern switch case has no binding"))?;
            for var in Expr::pattern_vars(&cx.ir, value) {
                cx.ir[var].write_flags.insert(WriteFlags::WRITING_PATTERN);
            }
        }
        _ => {}
    }
    buf.append_buffer(&write::to_java(cx, value, indent)?);
    Ok(())
}

fn write_guard(cx: &mut Cx, guard: Option<ExprId>, buf: &mut TextBuffer) -> io::Result<()> {
    if let Some(guard) = guard {
        buf.append(" when ")
            .append_buffer(&write::to_java(cx, guard, 0)?);
    }
    Ok(())
}

fn write_expression_arm(
    cx: &mut Cx,
    body: StatId,
    result_type: &VarType,
    indent: i32,
    buf: &mut TextBuffer,
) -> io::Result<()> {
    let simple = matches!(cx.ir[body].kind, StatementKind::BasicBlock { .. });
    if simple {
        let list = cx.ir[body]
            .exprents
            .ok_or_else(|| invalid("Switch expression block has no expression list"))?;
        if let &[expr] = cx.ir[list].as_slice() {
            let value = match cx.ir[expr].kind {
                ExprKind::Yield { value, .. } => {
                    set_constant_type(&mut cx.ir, value, result_type);
                    value
                }
                ExprKind::Exit {
                    kind: ExitType::Return,
                    ..
                } => {
                    return Err(invalid("Can't have return in switch expression"));
                }
                _ => expr,
            };
            buf.append_buffer(&write::to_java(cx, value, indent + 1)?)
                .append_char(';');
            return Ok(());
        }
    }

    buf.append_char('{')
        .append_line_separator()
        .append_buffer(&to_java(cx, body, indent + 2)?)
        .append_indent(indent + 1)
        .append_char('}');
    Ok(())
}

fn set_constant_type(ir: &mut Ir, expression: ExprId, ty: &VarType) {
    if let ExprKind::Constant { var_type, .. } = &mut ir[expression].kind
        && *var_type != VarType::VARTYPE_NULL
    {
        var_type.clone_from(ty);
    }
}

fn is_empty_default(ir: &Ir, stat: StatId) -> bool {
    matches!(ir[stat].kind, StatementKind::BasicBlock { .. })
        && ir[stat].exprents.is_some_and(|list| ir[list].is_empty())
        && stat.get_successor_edges(ir, EdgeType::Break.mask()).len() == 1
}

fn is_exhaustive(cx: &Cx, stat: StatId, selector_type: &VarType) -> bool {
    let labels: FxHashSet<&str> = switch(&cx.ir, stat)
        .case_values()
        .flatten()
        .flatten()
        .filter_map(|&label| match &cx.ir[label].kind {
            ExprKind::Field(field) if field.is_static() => Some(field.name.as_str()),
            _ => None,
        })
        .collect();
    selector_type
        .value
        .as_deref()
        .and_then(|name| cx.classes().get_class(name))
        .is_some_and(|class| {
            class.access_flags & ACC_ENUM != 0
                && class
                    .fields
                    .iter()
                    .filter(|field| field.access_flags & ACC_ENUM != 0)
                    .all(|field| labels.contains(field.name.as_str()))
        })
}

fn is_synthetic_throw_edge(cx: &Cx, edge: EdgeId) -> io::Result<bool> {
    let Some(list) = cx.ir[cx.ir[edge].destination].exprents else {
        return Ok(false);
    };
    let &[expr] = cx.ir[list].as_slice() else {
        return Ok(false);
    };
    let ExprKind::Exit {
        kind: ExitType::Throw,
        value,
        ..
    } = cx.ir[expr].kind
    else {
        return Ok(false);
    };
    let value = value.ok_or_else(|| invalid("Missing switch default throw operand"))?;
    let ty = Expr::expr_type(cx, value);
    let name = ty
        .value
        .as_deref()
        .ok_or_else(|| invalid("Missing switch default exception type"))?;
    Ok(matches!(
        name,
        "java/lang/IncompatibleClassChangeError" | "java/lang/MatchException"
    ))
}

fn head_expression(ir: &Ir, stat: StatId) -> io::Result<ExprId> {
    switch(ir, stat)
        .head_exprents
        .and_then(|list| ir[list].first().copied())
        .ok_or_else(|| invalid("Missing switch header"))
}

fn switch(ir: &Ir, stat: StatId) -> &SwitchStatement {
    let StatementKind::Switch(switch) = &ir[stat].kind else {
        unreachable!("Expected a switch statement");
    };
    switch
}
