// Copyright 2000-2024 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Operator spelling, grouping and typed function expressions.

use std::io;

use crate::decompiler::expr_processor::{get_cast_type_name, type_name};
use crate::decompiler::exps::{ConstantValue, Expr, ExprKind, FunctionType, WriteFlags, literal};
use crate::decompiler::ir::ExprId;
use crate::engine::Cx;
use crate::types::VarType;
use crate::util::text_buffer::TextBuffer;

use super::to_java;

impl FunctionType {
    fn java_syntax(self) -> (i32, &'static str) {
        use FunctionType::*;
        match self {
            ArrayLength => (0, ".length"),
            BitNot => (1, "~"),
            BoolNot => (1, "!"),
            Neg => (1, "-"),
            Imm | Mmi => (1, "--"),
            Ipp | Ppi => (1, "++"),
            Cast | I2l | I2f | I2d | L2i | L2f | L2d | F2i | F2l | F2d | D2i | D2l | D2f | I2b
            | I2c | I2s => (1, ""),
            Mul => (2, "*"),
            Div => (2, "/"),
            Rem => (2, "%"),
            Add | StrConcat => (3, "+"),
            Sub => (3, "-"),
            Shl => (4, "<<"),
            Shr => (4, ">>"),
            Ushr => (4, ">>>"),
            Lt => (5, "<"),
            Ge => (5, ">="),
            Gt => (5, ">"),
            Le => (5, "<="),
            Eq => (6, "=="),
            Ne => (6, "!="),
            InstanceOf => (6, "instanceof"),
            And => (7, "&"),
            Xor => (8, "^"),
            Or => (9, "|"),
            BoolAnd => (10, "&&"),
            BoolOr => (11, "||"),
            Ternary => (12, ""),
            Lcmp => (-1, "__lcmp__"),
            Fcmpl => (-1, "__fcmpl__"),
            Fcmpg => (-1, "__fcmpg__"),
            Dcmpl => (-1, "__dcmpl__"),
            Dcmpg => (-1, "__dcmpg__"),
            Other => unreachable!("Kotlin function has no Java syntax"),
        }
    }

    pub(crate) fn java_operator(self) -> &'static str {
        self.java_syntax().1
    }

    pub(crate) fn java_precedence(self) -> i32 {
        self.java_syntax().0
    }

    fn associative(self) -> bool {
        use FunctionType::*;
        matches!(
            self,
            Add | Mul | And | Or | Xor | BoolAnd | BoolOr | StrConcat
        )
    }
}

pub(crate) fn precedence(cx: &mut Cx, expr: ExprId) -> io::Result<i32> {
    if let Some(value) = crate::kotlin::body::precedence(cx, expr) {
        return Ok(value);
    }
    let expr = &cx.ir[expr];
    Ok(match &expr.kind {
        ExprKind::Constant {
            var_type, value, ..
        } => {
            let (ty, value, offsets) = (var_type.clone(), value.clone(), expr.bytecode.clone());
            literal::precedence(cx, &ty, &value, offsets.as_ref())
        }
        ExprKind::Function {
            op,
            operands,
            needs_cast,
            ..
        } => {
            if !needs_cast && (*op == FunctionType::Cast || op.simple_cast_type().is_some()) {
                return precedence(cx, operands[0]);
            }
            op.java_precedence()
        }
        ExprKind::Assignment { .. } => 13,
        ExprKind::New { .. } | ExprKind::Switch { .. } => 1,
        _ => 0,
    })
}

pub(super) fn function(cx: &mut Cx, expr: ExprId, indent: i32) -> io::Result<TextBuffer> {
    use FunctionType::*;
    let ExprKind::Function {
        op,
        operands,
        needs_cast,
        ..
    } = &cx.ir[expr].kind
    else {
        unreachable!("Expected a function expression")
    };
    let (op, operands, needs_cast) = (*op, operands.clone(), *needs_cast);
    if op == Other {
        return Err(std::io::Error::new(std::io::ErrorKind::InvalidData, "Missing Kotlin function renderer"));
    }
    let operator = op.java_operator();
    let mut buf = TextBuffer::new(cx);
    literal::add_offsets(&mut buf, cx.ir[expr].bytecode.as_ref());

    if op.is_arithmetic_binary() {
        let (left, right) = (operands[0], operands[1]);
        adjust_binary_constant(cx, left, right);
        let mut left_text = wrap_operand(cx, expr, left, false, indent, true)?;
        let mut right_text = wrap_operand(cx, expr, right, true, indent, true)?;
        if matches!(op, And | Or) {
            bit_mask(cx, right, &mut right_text);
            bit_mask(cx, left, &mut left_text);
        }
        let grouped = !cx.ir[expr].write_flags.contains(WriteFlags::UNGROUPED);
        if grouped {
            buf.push_newline_group(indent, 1);
        }
        buf.append_buffer(&left_text)
            .append_possible_newline_or(" ", false)
            .append(operator)
            .append(" ")
            .append_buffer(&right_text);
        if grouped {
            buf.pop_newline_group();
        }
        return Ok(buf);
    }

    match op {
        Eq | Ne | Lt | Ge | Gt | Le | BoolAnd | BoolOr | StrConcat => {
            let (left, right) = (operands[0], operands[1]);
            if matches!(op, Eq | Ne | Lt | Ge | Gt | Le) {
                adjust_binary_constant(cx, left, right);
            }
            let grouped = !cx.ir[expr].write_flags.contains(WriteFlags::UNGROUPED);
            if grouped {
                buf.push_newline_group(indent, 1);
            }
            buf.append_buffer(&wrap_operand(cx, expr, left, false, indent, true)?)
                .append_possible_newline_or(" ", false)
                .append(operator)
                .append(" ")
                .append_buffer(&wrap_operand(cx, expr, right, true, indent, true)?);
            if grouped {
                buf.pop_newline_group();
            }
        }
        BitNot | BoolNot | Neg | Mmi | Ppi => {
            let mut operand = wrap_operand(cx, expr, operands[0], true, indent, false)?;
            buf.append_buffer(operand.prepend(operator));
        }
        Ipp | Imm => {
            let mut operand = wrap_operand(cx, expr, operands[0], true, indent, false)?;
            buf.append_buffer(operand.append(operator));
        }
        Cast => {
            if needs_cast {
                for (index, &target) in operands[1..].iter().enumerate() {
                    if index > 0 {
                        buf.append(" & ");
                    }
                    buf.append_buffer(&to_java(cx, target, indent)?);
                }
                buf.enclose_with_parens().append_buffer(&wrap_operand(
                    cx,
                    expr,
                    operands[0],
                    true,
                    indent,
                    false,
                )?);
            } else {
                buf.append_buffer(&to_java(cx, operands[0], indent)?);
            }
        }
        ArrayLength => {
            let array = operands[0];
            buf.append_buffer(&wrap_operand(cx, expr, array, false, indent, false)?);
            if Expr::expr_type(cx, array).array_dim == 0 {
                let ty = VarType::VARTYPE_OBJECT.resize_array_dim(1);
                let array_type = get_cast_type_name(cx, &ty);
                buf.enclose(&format!("(({array_type})"), ")");
                buf.add_type_name_token(cx, &ty, 2);
            }
            buf.append(operator);
        }
        Ternary => {
            buf.push_newline_group(indent, 1);
            buf.append_buffer(&wrap_operand(cx, expr, operands[0], true, indent, false)?)
                .append_possible_newline_or(" ", false)
                .append("? ")
                .append_buffer(&wrap_operand(cx, expr, operands[1], true, indent, false)?)
                .append_possible_newline_or(" ", false)
                .append(": ")
                .append_buffer(&wrap_operand(cx, expr, operands[2], true, indent, false)?);
            buf.pop_newline_group();
        }
        InstanceOf => {
            buf.append_buffer(&wrap_operand(cx, expr, operands[0], true, indent, false)?)
                .append(" ")
                .append(operator)
                .append(" ");
            let target = if let Some(&pattern) = operands.get(2) {
                for var in Expr::pattern_vars(&cx.ir, pattern) {
                    cx.ir[var].write_flags.insert(WriteFlags::WRITING_PATTERN);
                }
                pattern
            } else {
                operands[1]
            };
            buf.append_buffer(&wrap_operand(cx, expr, target, true, indent, false)?);
        }
        Lcmp | Fcmpl | Fcmpg | Dcmpl | Dcmpg => {
            let mut left = wrap_operand(cx, expr, operands[0], true, indent, false)?;
            buf.append_buffer(left.prepend(&format!("{operator}(")))
                .append(", ")
                .append_buffer(&wrap_operand(cx, expr, operands[1], true, indent, false)?)
                .append(")");
        }
        I2l | I2f | I2d | L2i | L2f | L2d | F2i | F2l | F2d | D2i | D2l | D2f | I2b | I2c | I2s => {
            let operand = operands[0];
            if matches!(&cx.ir[operand].kind, ExprKind::Invocation(inv) if inv.is_unboxing_call()) {
                cx.ir[operand]
                    .write_flags
                    .insert(WriteFlags::FORCE_UNBOXING);
            }
            if needs_cast {
                let ty = op.simple_cast_type().unwrap();
                buf.append(&type_name(cx, &ty, true))
                    .enclose_with_parens()
                    .append_buffer(&wrap_operand(cx, expr, operand, true, indent, false)?);
            } else {
                buf.append_buffer(&to_java(cx, operand, indent)?);
            }
        }
        Add | Sub | Mul | Div | And | Or | Xor | Rem | Shl | Shr | Ushr | Other => unreachable!(),
    }
    Ok(buf)
}

fn adjust_binary_constant(cx: &mut Cx, left: ExprId, right: ExprId) {
    if matches!(cx.ir[right].kind, ExprKind::Constant { .. }) {
        let ty = Expr::expr_type(cx, left);
        literal::adjust_const_type(&mut cx.ir, right, &ty);
    } else if matches!(cx.ir[left].kind, ExprKind::Constant { .. }) {
        let ty = Expr::expr_type(cx, right);
        literal::adjust_const_type(&mut cx.ir, left, &ty);
    }
}

fn bit_mask(cx: &Cx, expr: ExprId, buf: &mut TextBuffer) {
    if let ExprKind::Constant {
        value: ConstantValue::Integer(value),
        var_type,
        ..
    } = &cx.ir[expr].kind
        && *var_type == VarType::VARTYPE_INT
    {
        buf.set_length(0);
        match *value as u32 {
            0xff => buf.append("0xFF"),
            0xff00 => buf.append("0xFF00"),
            0xff0000 => buf.append("0xFF0000"),
            0xff000000 => buf.append("0xFF000000"),
            _ => buf.append_int(*value),
        };
    }
}

pub(crate) fn wrap_operand(
    cx: &mut Cx,
    function: ExprId,
    operand: ExprId,
    quote_equal: bool,
    indent: i32,
    merge_group: bool,
) -> io::Result<TextBuffer> {
    let parent_precedence = precedence(cx, function)?;
    let child_precedence = precedence(cx, operand)?;
    let same_precedence = child_precedence == parent_precedence;
    let mut parentheses = child_precedence > parent_precedence;
    if quote_equal && same_precedence {
        let ExprKind::Function { op, .. } = cx.ir[function].kind else {
            unreachable!()
        };
        parentheses = true;
        if matches!(cx.ir[operand].kind, ExprKind::Function { op: child, .. } if child == op) {
            let ty = Expr::expr_type(cx, operand);
            if ty != VarType::VARTYPE_FLOAT && ty != VarType::VARTYPE_DOUBLE && op.associative() {
                parentheses = false;
            }
        }
    }

    if merge_group
        && !parentheses
        && same_precedence
        && let ExprKind::Function {
            op,
            operands,
            needs_cast,
            ..
        } = &cx.ir[operand].kind
    {
        let mut child = operand;
        if *op == FunctionType::Cast
            && !needs_cast
            && matches!(cx.ir[operands[0]].kind, ExprKind::Function { .. })
        {
            child = operands[0];
        }
        cx.ir[child].write_flags.insert(WriteFlags::UNGROUPED);
    }

    let rendered = to_java(cx, operand, indent)?;
    if !parentheses {
        return Ok(rendered);
    }
    let mut buf = TextBuffer::from_text(cx, "(");
    buf.push_newline_group(indent, 1)
        .append_possible_newline()
        .append_buffer(&rendered)
        .append_possible_newline_or("", true);
    buf.pop_newline_group();
    buf.append(")");
    Ok(buf)
}
