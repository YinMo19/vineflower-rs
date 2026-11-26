// SPDX-License-Identifier: Apache-2.0

//! Expression subclass writers. A superclass call bypasses the dispatch
//! for its own handle while retaining the children's dynamic types.

use std::io;

use crate::decompiler::exps::{ExitType, Expr, ExprKind, FunctionType, literal, write};
use crate::decompiler::ir::ExprId;
use crate::decompiler::vars::versions::FinalType;
use crate::engine::Cx;
use crate::kotlin::{identifier, types::kotlin_type};
use crate::structs::consts::ConstantValue;
use crate::types::{CodeType, TypeFamily, VarType};
use crate::util::text_buffer::TextBuffer;

use super::{Declaration, InvocationStyle, KotlinExpr, KotlinFunction};

pub(crate) fn precedence(cx: &Cx, expr: ExprId) -> Option<i32> {
    Some(match cx.kotlin_expr(expr)? {
        KotlinExpr::Function(Some(op)) => match op {
            KotlinFunction::IdentityEquals => 6,
            KotlinFunction::Elvis => 11,
            KotlinFunction::GetKClass => 1,
            KotlinFunction::StringTemplate => FunctionType::StrConcat.java_precedence(),
        },
        KotlinExpr::Invocation(Some(InvocationStyle::Infix { .. })) => 9,
        KotlinExpr::New { .. } => 0,
        _ => return None,
    })
}

pub(crate) fn write_expression(
    cx: &mut Cx,
    expr: ExprId,
    indent: i32,
    wrapper: KotlinExpr,
) -> io::Result<TextBuffer> {
    match wrapper {
        KotlinExpr::Constant { unsigned } => constant(cx, expr, indent, unsigned),
        KotlinExpr::Variable(declaration) => variable(cx, expr, declaration),
        KotlinExpr::Function(op) => function(cx, expr, indent, op),
        KotlinExpr::Invocation(style) => invocation(cx, expr, indent, style),
        KotlinExpr::Field => field(cx, expr, indent),
        KotlinExpr::SwitchHead => {
            let ExprKind::SwitchHead { value, .. } = cx.ir[expr].kind else {
                unreachable!()
            };
            let mut result = write::to_java(cx, value, indent)?;
            result.enclose("when (", ")");
            if let Some(offsets) = &cx.ir[expr].bytecode {
                for offset in offsets.iter() {
                    result.add_start_bytecode_mapping(offset as i32);
                }
            }
            Ok(result)
        }
        KotlinExpr::Exit { lambda_name } => exit(cx, expr, indent, lambda_name.as_deref()),
        KotlinExpr::New { in_annotation } => {
            super::allocation::allocation(cx, expr, indent, in_annotation)
        }
    }
}

fn constant(
    cx: &mut Cx,
    expr: ExprId,
    indent: i32,
    unsigned: Option<CodeType>,
) -> io::Result<TextBuffer> {
    let ExprKind::Constant {
        value, var_type, ..
    } = &cx.ir[expr].kind
    else {
        unreachable!()
    };
    if *var_type == VarType::VARTYPE_CLASS
        && let ConstantValue::String(name) = value
    {
        let name = name.as_utf8_lossy().clone();
        let mut result = mapped_buffer(cx, expr);
        append_class_literal(cx, &mut result, &name);
        return Ok(result);
    }
    if matches!(value, ConstantValue::Null) && *var_type != VarType::VARTYPE_NULL {
        let ty = var_type.clone();
        let mut result = mapped_buffer(cx, expr);
        result.append(&kotlin_type(cx, Some(&ty), true)?);
        return Ok(result);
    }
    if let Some(ty) = unsigned {
        let (number, suffix) = match (ty, value) {
            (CodeType::Long, ConstantValue::Long(value)) => (*value as u64, "uL"),
            (CodeType::Byte, ConstantValue::Integer(value)) => ((*value as u8).into(), "u"),
            (CodeType::Short, ConstantValue::Integer(value)) => ((*value as u16).into(), "u"),
            (CodeType::Int, ConstantValue::Integer(value)) => ((*value as u32).into(), "u"),
            _ => return Err(invalid("Unknown Kotlin unsigned constant type")),
        };
        let mut result = mapped_buffer(cx, expr);
        result.append(&number.to_string()).append(suffix);
        return Ok(result);
    }
    write::java_to_java(cx, expr, indent)
}

/// KConstExprent.toJava on a JVM class literal, including boxed primitive handles.
pub(crate) fn append_class_literal(cx: &mut Cx, buffer: &mut TextBuffer, name: &str) {
    let ty = VarType::from_signature_cl(name, !name.starts_with('['));
    buffer.append_cast_type_name(cx, &ty).append("::class.java");
    if primitive_box(name) {
        buffer.append("ObjectType");
    }
}

fn primitive_box(class: &str) -> bool {
    matches!(
        class,
        "java/lang/Boolean"
            | "java/lang/Byte"
            | "java/lang/Character"
            | "java/lang/Short"
            | "java/lang/Integer"
            | "java/lang/Long"
            | "java/lang/Float"
            | "java/lang/Double"
            | "java/lang/Void"
    )
}

fn variable(cx: &mut Cx, expr: ExprId, declaration: Declaration) -> io::Result<TextBuffer> {
    let var = Expr::variable(&cx.ir, expr)
        .expect("Expected a Kotlin variable")
        .clone();
    let processor = var.processor.map(|owner| &cx.ir[owner]);
    let pair = var.pair();
    let mut result = mapped_buffer(cx, expr);
    if declaration == Declaration::Definition {
        let is_final = var.effectively_final
            || processor.is_some_and(|proc| {
                proc.versions.final_vars.get(&pair) != Some(&FinalType::NonFinal)
            });
        result.append(if is_final { "val " } else { "var " });
    }
    result.append(&variable_name(cx, &var));
    if matches!(
        declaration,
        Declaration::Definition | Declaration::Exception
    ) {
        let ty = crate::decompiler::exps::write::variable_definition_type(cx, expr, &var);
        result
            .append(": ")
            .append(&kotlin_type(cx, Some(&ty), true)?);
    }
    Ok(result)
}

pub(super) fn variable_name(cx: &Cx, var: &crate::decompiler::exps::Variable) -> String {
    let pair = var.pair();
    let processor = var.processor.map(|owner| &cx.ir[owner]);
    let name = processor
        .and_then(|proc| proc.clashing_names.get(&pair))
        .or_else(|| {
            var.lvt
                .as_ref()
                .filter(|_| cx.options.use_lvt_names)
                .map(|lvt| lvt.get_name())
        })
        .or_else(|| processor.and_then(|proc| proc.names.get(&pair).and_then(Option::as_ref)));
    if let Some(name) = name {
        if name == "this" || name.starts_with("this@") {
            name.to_string()
        } else {
            identifier(name).into_owned()
        }
    } else if pair.version == 0 {
        format!("var{}", pair.var)
    } else {
        format!("var{}_{}", pair.var, pair.version)
    }
}

fn exit(
    cx: &mut Cx,
    expr: ExprId,
    indent: i32,
    lambda_name: Option<&str>,
) -> io::Result<TextBuffer> {
    let ExprKind::Exit {
        kind,
        value,
        return_type,
        ..
    } = &cx.ir[expr].kind
    else {
        unreachable!()
    };
    if *kind == ExitType::Throw || cx.writing_method().is_none() {
        return write::java_to_java(cx, expr, indent);
    }
    let mut result = TextBuffer::new(cx);
    if let Some(name) = lambda_name {
        result.append("return@").append(name);
        if return_type
            .as_ref()
            .is_some_and(|ty| ty.ty == CodeType::Void || ty.name() == "kotlin/Unit")
        {
            return Ok(result);
        }
        result.append_char(' ');
    }
    let value = value.ok_or_else(|| invalid("Kotlin return expression has no value"))?;
    result.append_buffer(&write::to_java(cx, value, indent)?);
    Ok(result)
}

fn field(cx: &mut Cx, expr: ExprId, indent: i32) -> io::Result<TextBuffer> {
    let ExprKind::Field(field) = &cx.ir[expr].kind else {
        unreachable!()
    };
    if field.name == "TYPE"
        && let Some(owner) = field
            .classname
            .as_deref()
            .filter(|owner| primitive_box(owner))
    {
        let ty = VarType::from_signature_cl(owner, true);
        let mut result = mapped_buffer(cx, expr);
        result
            .append(&kotlin_type(cx, Some(&ty), true)?)
            .append("::class.javaPrimitiveType");
        return Ok(result);
    }
    if let Some(value) = crate::kotlin::writer::field_expression(cx, expr, indent)? {
        return Ok(value);
    }
    write::java_to_java(cx, expr, indent)
}

fn invocation(
    cx: &mut Cx,
    expr: ExprId,
    indent: i32,
    style: Option<InvocationStyle>,
) -> io::Result<TextBuffer> {
    let ExprKind::Invocation(call) = &cx.ir[expr].kind else {
        unreachable!()
    };
    let (instance, owner, method, descriptor) = (
        call.instance,
        call.classname.clone(),
        call.name.clone(),
        call.descriptor.clone(),
    );
    match style {
        Some(InvocationStyle::Property { name, method }) => {
            use crate::kotlin::members::PropertyMethod;
            let method =
                method.ok_or_else(|| invalid("Kotlin property invocation has no accessor kind"))?;
            let value = call.parameters.first().copied();
            let mut result = mapped_buffer(cx, expr);
            if let Some(receiver) = instance {
                result
                    .append_buffer(&receiver_expression(cx, expr, receiver, indent)?)
                    .append_char('.');
            }
            result.append(&name);
            if method == PropertyMethod::Setter {
                let value =
                    value.ok_or_else(|| invalid("Kotlin property setter has no argument"))?;
                result
                    .append(" = ")
                    .append_buffer(&write::to_java(cx, value, indent)?);
            }
            Ok(result)
        }
        Some(InvocationStyle::Infix { name, extension }) => {
            let receiver = if extension {
                call.parameters.first().copied()
            } else {
                instance
            };
            let arg = call.parameters.get(usize::from(extension)).copied();
            let receiver = receiver.ok_or_else(|| invalid("Kotlin infix call has no receiver"))?;
            let arg = arg.ok_or_else(|| invalid("Kotlin infix call has no argument"))?;
            let mut result = mapped_buffer(cx, expr);
            result
                .append_buffer(&receiver_expression(cx, expr, receiver, indent)?)
                .append_char(' ')
                .append(&name)
                .append_char(' ')
                .append_buffer(&write::to_java(cx, arg, indent)?);
            Ok(result)
        }
        None => {
            if let Some(owner) = owner
                .as_deref()
                .filter(|owner| owner.starts_with("kotlin/jvm/functions/Function"))
            {
                let receiver =
                    instance.ok_or_else(|| invalid("Kotlin function call has no receiver"))?;
                let empty = call.parameters.is_empty();
                let mut result = receiver_expression(cx, expr, receiver, indent)?;
                if empty {
                    result.append_method_with("()", false, owner, &method, (*descriptor).clone());
                } else {
                    result
                        .append_method_with("(", false, owner, &method, (*descriptor).clone())
                        .append_buffer(&write::append_param_list(cx, expr, indent)?)
                        .append_method_with(")", false, owner, &method, (*descriptor).clone());
                }
                literal::add_offsets(&mut result, cx.ir[expr].bytecode.as_ref());
                Ok(result)
            } else {
                write::java_to_java(cx, expr, indent)
            }
        }
    }
}

fn receiver_expression(
    cx: &mut Cx,
    call: ExprId,
    receiver: ExprId,
    indent: i32,
) -> io::Result<TextBuffer> {
    let mut result = write::to_java(cx, receiver, indent)?;
    if write::precedence(cx, receiver)? > write::precedence(cx, call)? {
        result.enclose_with_parens();
    }
    Ok(result)
}

fn function(
    cx: &mut Cx,
    expr: ExprId,
    indent: i32,
    kotlin_op: Option<KotlinFunction>,
) -> io::Result<TextBuffer> {
    use FunctionType::*;
    let mut result = mapped_buffer(cx, expr);
    let ExprKind::Function {
        op,
        operands,
        needs_cast,
        ..
    } = &cx.ir[expr].kind
    else {
        unreachable!()
    };
    let (mut op, operands, needs_cast) = (*op, operands.clone(), *needs_cast);
    let mut kotlin_op = kotlin_op;
    if kotlin_op == Some(KotlinFunction::IdentityEquals)
        && operands
            .iter()
            .any(|&operand| Expr::expr_type(cx, operand).type_family != TypeFamily::Object)
    {
        let ExprKind::Function { op: current, .. } = &mut cx.ir[expr].kind else {
            unreachable!()
        };
        *current = Eq;
        op = Eq;
        kotlin_op = None;
        cx.set_kotlin_expr(expr, KotlinExpr::Function(None));
    }
    match op {
        Other => match kotlin_op.ok_or_else(|| invalid("Missing Kotlin function operator"))? {
            KotlinFunction::IdentityEquals => infix(
                cx,
                &mut result,
                expr,
                indent,
                operands[0],
                " === ",
                operands[1],
            )?,
            KotlinFunction::Elvis => infix(
                cx,
                &mut result,
                expr,
                indent,
                operands[0],
                " ?: ",
                operands[1],
            )?,
            KotlinFunction::GetKClass => get_kclass(cx, operands[0], &mut result)?,
            KotlinFunction::StringTemplate => string_template(cx, &operands, indent, &mut result)?,
        },
        Ternary => {
            let [condition, yes, no] = operands[..] else {
                unreachable!()
            };
            if cx.kotlin_expr(condition).is_some()
                && matches!(
                    cx.ir[condition].kind,
                    ExprKind::Function { op: InstanceOf, .. }
                )
                && cx.kotlin_expr(yes).is_some()
                && let ExprKind::Function {
                    op: Cast,
                    operands: params,
                    ..
                } = &cx.ir[yes].kind
                && Expr::expr_type(cx, no) == VarType::VARTYPE_NULL
            {
                let (value, ty) = (params[0], params[1]);
                result
                    .append_buffer(&write::to_java(cx, value, indent)?)
                    .append(" as? ")
                    .append_buffer(&write::to_java(cx, ty, indent)?);
            } else {
                result.push_newline_group(indent, 1);
                result
                    .append("if (")
                    .append_buffer(&write::wrap_operand(
                        cx, expr, condition, true, indent, false,
                    )?)
                    .append(")")
                    .append_possible_newline_or(" ", false)
                    .append_buffer(&write::wrap_operand(cx, expr, yes, true, indent, false)?)
                    .append_possible_newline_or(" ", false)
                    .append("else")
                    .append_possible_newline_or(" ", false)
                    .append_buffer(&write::wrap_operand(cx, expr, no, true, indent, false)?);
                result.pop_newline_group();
            }
        }
        InstanceOf => infix(
            cx,
            &mut result,
            expr,
            indent,
            operands[0],
            " is ",
            operands[1],
        )?,
        BoolNot
            if cx.kotlin_expr(operands[0]).is_some()
                && matches!(
                    cx.ir[operands[0]].kind,
                    ExprKind::Function { op: InstanceOf, .. }
                ) =>
        {
            let ExprKind::Function { operands, .. } = &cx.ir[operands[0]].kind else {
                unreachable!()
            };
            infix(
                cx,
                &mut result,
                expr,
                indent,
                operands[0],
                " !is ",
                operands[1],
            )?;
        }
        And => infix(
            cx,
            &mut result,
            expr,
            indent,
            operands[0],
            " and ",
            operands[1],
        )?,
        Or => infix(
            cx,
            &mut result,
            expr,
            indent,
            operands[0],
            " or ",
            operands[1],
        )?,
        Xor => infix(
            cx,
            &mut result,
            expr,
            indent,
            operands[0],
            " xor ",
            operands[1],
        )?,
        Shl => infix(
            cx,
            &mut result,
            expr,
            indent,
            operands[0],
            " shl ",
            operands[1],
        )?,
        Shr => infix(
            cx,
            &mut result,
            expr,
            indent,
            operands[0],
            " shr ",
            operands[1],
        )?,
        Ushr => infix(
            cx,
            &mut result,
            expr,
            indent,
            operands[0],
            " ushr ",
            operands[1],
        )?,
        Cast => {
            if needs_cast {
                result
                    .append_buffer(&write::wrap_operand(
                        cx,
                        expr,
                        operands[0],
                        true,
                        indent,
                        false,
                    )?)
                    .append(" as ")
                    .append_buffer(&write::to_java(cx, operands[1], indent)?);
            } else {
                result.append_buffer(&write::to_java(cx, operands[0], indent)?);
            }
        }
        BitNot => {
            result
                .append_buffer(&write::wrap_operand(
                    cx,
                    expr,
                    operands[0],
                    true,
                    indent,
                    false,
                )?)
                .append(".inv()");
        }
        _ => {
            result.append_buffer(&write::java_to_java(cx, expr, indent)?);
        }
    }
    Ok(result)
}

fn infix(
    cx: &mut Cx,
    result: &mut TextBuffer,
    function: ExprId,
    indent: i32,
    lhs: ExprId,
    operator: &str,
    rhs: ExprId,
) -> io::Result<()> {
    result
        .append_buffer(&write::wrap_operand(
            cx, function, lhs, true, indent, false,
        )?)
        .append(operator)
        .append_buffer(&write::wrap_operand(
            cx, function, rhs, true, indent, false,
        )?);
    Ok(())
}

fn get_kclass(cx: &mut Cx, expr: ExprId, result: &mut TextBuffer) -> io::Result<()> {
    match &cx.ir[expr].kind {
        ExprKind::Variable(variable) => {
            if variable.expr_type(cx) != VarType::VARTYPE_CLASS {
                return Err(invalid("Variable accessing KClass is not a Class"));
            }
            result
                .append_buffer(&write::to_java(cx, expr, 0)?)
                .append(".kotlin");
            return Ok(());
        }
        ExprKind::Constant {
            value: ConstantValue::String(name),
            ..
        } => {
            let name = name.as_utf8_lossy();
            let ty = VarType::from_signature_cl(name, !name.starts_with('['));
            result.append(&kotlin_type(cx, Some(&ty), true)?);
        }
        ExprKind::Field(field) => {
            let class = field
                .classname
                .as_deref()
                .ok_or_else(|| invalid("KClass field has no owner"))?;
            let ty = VarType::from_signature_cl(class, true);
            result.append(&kotlin_type(cx, Some(&ty), true)?);
        }
        _ => {
            result.append_buffer(&write::to_java(cx, expr, 0)?);
        }
    }
    result.append("::class");
    Ok(())
}

fn string_template(
    cx: &mut Cx,
    operands: &[ExprId],
    indent: i32,
    result: &mut TextBuffer,
) -> io::Result<()> {
    result.append_char('"');
    for &expr in operands {
        match &cx.ir[expr].kind {
            ExprKind::Constant {
                value: ConstantValue::String(value),
                var_type,
                ..
            } if *var_type == VarType::VARTYPE_STRING => {
                let value = literal::escape_string(value, cx.options.ascii_strings);
                result.append(&value.replace('$', "\\$"));
            }
            ExprKind::Constant {
                value: ConstantValue::Integer(value),
                var_type,
                ..
            } if *var_type == VarType::VARTYPE_CHAR => {
                result.append_utf16_unit(*value as u16);
            }
            ExprKind::Variable(_) => {
                result
                    .append_char('$')
                    .append_buffer(&write::to_java(cx, expr, indent)?);
            }
            _ => {
                if matches!(&cx.ir[expr].kind, ExprKind::Constant { var_type, .. } if VarType::is_primitive(var_type))
                {
                    log::warn!(
                        "Primitive constant type in string concatenation: {}",
                        Expr::expr_type(cx, expr)
                    );
                }
                result
                    .append("${")
                    .append_buffer(&write::to_java(cx, expr, indent)?)
                    .append_char('}');
            }
        }
    }
    result.append_char('"');
    Ok(())
}

fn mapped_buffer(cx: &Cx, expr: ExprId) -> TextBuffer {
    let mut result = TextBuffer::new(cx);
    literal::add_offsets(&mut result, cx.ir[expr].bytecode.as_ref());
    result
}

fn invalid(message: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}
