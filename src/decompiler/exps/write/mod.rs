// Copyright 2000-2024 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Expression rendering retains the operand's IR identity through recursive
//! calls so inference, qualifier state and source mappings follow the JVM tree.

mod allocation;
mod assignment;
pub(crate) mod casts;
mod fields;
mod functions;
mod invocation;
mod lambda_types;
mod variables;

use std::io;

use super::{ExitType, Expr, ExprKind, MonitorType, generic_inference::Inference, literal};
use crate::decompiler::ir::ExprId;
use crate::engine::Cx;
use crate::types::{CodeType, VarType};
use crate::util::text_buffer::TextBuffer;
use casts::{CastOptions, NullCastType, append_casted};
pub(crate) use functions::precedence;

pub fn to_java(cx: &mut Cx, expr: ExprId, indent: i32) -> io::Result<TextBuffer> {
    let mut buf = TextBuffer::new(cx);
    match &cx.ir[expr].kind {
        ExprKind::Function { .. } => return functions::function(cx, expr, indent),
        ExprKind::Field(_) => return fields::to_java(cx, expr, indent),
        ExprKind::Variable(_) => return variables::to_java(cx, expr, indent),
        ExprKind::Assignment { .. } => return assignment::to_java(cx, expr, indent),
        ExprKind::Invocation(_) => return invocation::invocation(cx, expr, indent),
        ExprKind::New { .. } => return allocation::to_java(cx, expr, indent),
        ExprKind::Constant {
            value,
            var_type,
            was_condy,
            ..
        } => {
            let (ty, value, condy) = (var_type.clone(), value.clone(), *was_condy);
            let offsets = cx.ir[expr].bytecode.clone();
            return literal::render(cx, &ty, &value, offsets.as_ref(), condy);
        }
        ExprKind::Array { array, index, .. } => {
            let (array, index) = (*array, *index);
            buf = to_java(cx, array, indent)?;
            if precedence(cx, array)? > 0
                && !matches!(&cx.ir[array].kind,
                ExprKind::New { direct_array_init, array_elements, .. } if *direct_array_init || !array_elements.is_empty())
            {
                buf.enclose_with_parens();
            }
            if Expr::expr_type(cx, array).array_dim == 0 {
                let array_ty = VarType::VARTYPE_OBJECT.resize_array_dim(1);
                let name = crate::decompiler::expr_processor::get_cast_type_name(cx, &array_ty);
                buf.enclose(&format!("(({name})"), ")");
                buf.add_type_name_token(cx, &array_ty, 2);
            }
            literal::add_offsets(&mut buf, cx.ir[expr].bytecode.as_ref());
            buf.append_char('[')
                .append_buffer(&to_java(cx, index, indent)?)
                .append_char(']');
        }
        ExprKind::Exit {
            kind,
            value,
            return_type,
            method_descriptor,
        } => {
            let (kind, value, ty, desc) = (
                *kind,
                *value,
                return_type.clone(),
                method_descriptor.clone(),
            );
            literal::add_offsets(&mut buf, cx.ir[expr].bytecode.as_ref());
            match kind {
                ExitType::Return => {
                    buf.append("return");
                    let ty = ty.ok_or_else(|| invalid("Return expression without return type"))?;
                    if ty.ty != CodeType::Void {
                        let ty = desc
                            .generic_info()
                            .map_or(ty, |s| s.get().return_type.clone());
                        buf.append_char(' ');
                        append_casted(
                            cx,
                            required_value(value)?,
                            &ty,
                            &mut buf,
                            indent,
                            without_null_cast(),
                        )?;
                    }
                }
                ExitType::Throw => {
                    let value = required_value(value)?;
                    if let Some(ty) = declared_throw_type(cx) {
                        buf.append("throw ");
                        append_casted(cx, value, &ty, &mut buf, indent, CastOptions::default())?;
                    } else {
                        buf.append_buffer(&to_java(cx, value, indent)?)
                            .prepend("throw ");
                    }
                }
            }
        }
        ExprKind::Assert { condition, message } => {
            let (condition, message) = (*condition, *message);
            buf.append("assert ");
            literal::add_offsets(&mut buf, cx.ir[expr].bytecode.as_ref());
            if let Some(condition) = condition {
                buf.append_buffer(&to_java(cx, condition, indent)?);
            } else {
                buf.append("false");
            }
            if let Some(message) = message {
                buf.append(" : ")
                    .append_buffer(&to_java(cx, message, indent)?);
            }
        }
        ExprKind::Monitor { kind, value, .. } => {
            let (kind, value) = (*kind, *value);
            literal::add_offsets(&mut buf, cx.ir[expr].bytecode.as_ref());
            if kind == MonitorType::Enter {
                if matches!(&cx.ir[value].kind, ExprKind::Constant { var_type, .. } if *var_type == VarType::VARTYPE_NULL)
                {
                    log::warn!("Created invalid synchronize on null!");
                }
                buf.append_buffer(&to_java(cx, value, indent)?)
                    .enclose("synchronized (", ")");
            } else {
                buf.append("// $VF: monitorexit");
            }
        }
        ExprKind::If { condition } => {
            let condition = *condition;
            Inference::for_writing(cx).infer(condition, Some(&VarType::VARTYPE_BOOLEAN))?;
            buf = to_java(cx, condition, indent)?;
            buf.push_newline_group(indent, 1)
                .append_possible_newline()
                .enclose("if (", ")")
                .append_possible_newline_or("", true)
                .pop_newline_group();
            start_offsets(cx, expr, &mut buf);
        }
        ExprKind::SwitchHead { value, .. } => {
            buf = to_java(cx, *value, indent)?;
            buf.enclose("switch (", ")");
            start_offsets(cx, expr, &mut buf);
        }
        ExprKind::Yield { value, return_type } => {
            let (value, ty) = (*value, return_type.clone());
            buf.append("yield ");
            append_casted(cx, value, &ty, &mut buf, indent, without_null_cast())?;
        }
        ExprKind::Switch { .. } => {
            return crate::decompiler::stats::write::switch_expression(cx, expr, indent);
        }
        ExprKind::Pattern(pattern) => {
            let (ty, children) = (pattern.var_type.clone(), pattern.children.clone());
            buf.append_cast_type_name(cx, &ty).append_char('(');
            for (i, child) in children.into_iter().enumerate() {
                if i > 0 {
                    buf.append(", ");
                }
                buf.append_buffer(&to_java(cx, child, 0)?);
            }
            buf.append_char(')');
        }
    }
    Ok(buf)
}

fn start_offsets(cx: &Cx, expr: ExprId, buf: &mut TextBuffer) {
    for offset in cx.ir[expr].bytecode.iter().flat_map(|s| s.iter()) {
        buf.add_start_bytecode_mapping(offset as i32);
    }
}

fn without_null_cast() -> CastOptions {
    CastOptions {
        null_cast: NullCastType::DontCastAtAll,
        ..Default::default()
    }
}

fn required_value(value: Option<ExprId>) -> io::Result<ExprId> {
    value.ok_or_else(|| invalid("Missing exit expression operand"))
}

fn declared_throw_type(cx: &Cx) -> Option<VarType> {
    let class = &cx.class_nodes[cx.current_node()?].class;
    let exceptions = cx.writing_method()?.method.attributes.exceptions.as_ref()?;
    let mut chosen = None;
    for index in 0..exceptions.throws_exceptions.len() {
        let name = exceptions.get_exc_classname(index, &class.pool);
        match name.as_str() {
            "java/lang/Throwable" => return Some(VarType::from_signature_cl(&name, true)),
            "java/lang/Exception" => chosen = Some(VarType::from_signature_cl(&name, true)),
            _ => {}
        }
    }
    chosen
}

fn invalid(message: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}
