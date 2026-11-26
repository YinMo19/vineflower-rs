// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! The operations represented by `FunctionExprent` during expression lifting.

use crate::decompiler::ir::ExprId;
use crate::engine::Cx;
use crate::types::{CodeType, VarType};

use super::{Expr, ExprKind};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FunctionType {
    Add,
    Sub,
    Mul,
    Div,
    And,
    Or,
    Xor,
    Rem,
    Shl,
    Shr,
    Ushr,
    BitNot,
    BoolNot,
    Neg,
    I2l,
    I2f,
    I2d,
    L2i,
    L2f,
    L2d,
    F2i,
    F2l,
    F2d,
    D2i,
    D2l,
    D2f,
    I2b,
    I2c,
    I2s,
    Cast,
    InstanceOf,
    ArrayLength,
    Imm,
    Mmi,
    Ipp,
    Ppi,
    Ternary,
    Lcmp,
    Fcmpl,
    Fcmpg,
    Dcmpl,
    Dcmpg,
    Eq,
    Ne,
    Lt,
    Ge,
    Gt,
    Le,
    BoolAnd,
    BoolOr,
    StrConcat,
    Other,
}

impl FunctionType {
    pub const fn arity(self) -> usize {
        use FunctionType::*;
        match self {
            BitNot | BoolNot | Neg | I2l | I2f | I2d | L2i | L2f | L2d | F2i | F2l | F2d | D2i
            | D2l | D2f | I2b | I2c | I2s | ArrayLength | Imm | Mmi | Ipp | Ppi => 1,
            Ternary => 3,
            Other => 0,
            _ => 2,
        }
    }

    pub(crate) const fn is_arithmetic_binary(self) -> bool {
        use FunctionType::*;
        matches!(self, Add | Sub | Mul | Div | And | Or | Xor | Rem | Shl | Shr | Ushr)
    }

    pub const fn is_inc_dec(self) -> bool {
        matches!(self, Self::Imm | Self::Mmi | Self::Ipp | Self::Ppi)
    }

    pub(crate) fn simple_cast_type(self) -> Option<VarType> {
        use FunctionType::*;
        Some(match self {
            L2i | F2i | D2i => VarType::VARTYPE_INT,
            I2l | F2l | D2l => VarType::VARTYPE_LONG,
            I2f | L2f | D2f => VarType::VARTYPE_FLOAT,
            I2d | L2d | F2d => VarType::VARTYPE_DOUBLE,
            I2b => VarType::VARTYPE_BYTE,
            I2c => VarType::VARTYPE_CHAR,
            I2s => VarType::VARTYPE_SHORT,
            _ => return None,
        })
    }

    pub(super) fn expr_type(
        self,
        cx: &Cx,
        operands: &[ExprId],
        implicit_type: Option<&VarType>,
    ) -> VarType {
        use FunctionType::*;
        let operand_type = |index: usize| Expr::expr_type(cx, operands[index]);
        match self {
            StrConcat => VarType::VARTYPE_STRING,
            Other => unreachable!("Missing Kotlin function type"),
            ArrayLength => VarType::VARTYPE_INT,
            I2l | I2f | I2d | L2i | L2f | L2d | F2i | F2l | F2d | D2i | D2l | D2f
            | I2b | I2c | I2s => self.simple_cast_type().unwrap(),
            // Vineflower's temporary compare operations have boolean expression
            // type even though the JVM comparison instructions produce an int.
            Lcmp | Fcmpl | Fcmpg | Dcmpl | Dcmpg | Eq | Ne | Lt | Ge | Gt | Le | InstanceOf
            | BoolNot | BoolAnd | BoolOr => VarType::VARTYPE_BOOLEAN,
            Imm | Mmi | Ipp | Ppi => implicit_type
                .expect("Missing increment or decrement expression type")
                .clone(),
            Shl | Shr | Ushr | BitNot | Neg => max_numeric_type(&[operand_type(0)]),
            Add | Sub | Mul | Div | Rem => max_numeric_type(&[operand_type(0), operand_type(1)]),
            And | Or | Xor => {
                let left = operand_type(0);
                let right = operand_type(1);
                if left.ty == CodeType::Boolean && right.ty == CodeType::Boolean {
                    VarType::VARTYPE_BOOLEAN
                } else {
                    max_numeric_type(&[left, right])
                }
            }
            Cast => operand_type(1),
            Ternary => {
                let supertype = VarType::join(cx, &operand_type(1), &operand_type(2))
                    .expect("No common supertype for ternary expression");
                if operands[1..=2]
                    .iter()
                    .all(|&operand| matches!(cx.ir[operand].kind, ExprKind::Constant { .. }))
                    && supertype.ty != CodeType::Boolean
                    && VarType::VARTYPE_INT.higher_equal_in_lattice_than(cx, &supertype)
                {
                    VarType::VARTYPE_INT
                } else {
                    supertype
                }
            }
        }
    }
}

fn max_numeric_type(operands: &[VarType]) -> VarType {
    [
        VarType::VARTYPE_DOUBLE,
        VarType::VARTYPE_FLOAT,
        VarType::VARTYPE_LONG,
    ]
    .into_iter()
    .find(|ty| operands.iter().any(|operand| operand.ty == ty.ty))
    .unwrap_or(VarType::VARTYPE_INT)
}
