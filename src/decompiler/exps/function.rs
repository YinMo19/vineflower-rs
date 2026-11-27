//! The operations represented by `FunctionExprent` during expression lifting.

use crate::decompiler::ir::ExprId;
use crate::engine::Cx;
use crate::types::{CodeType, VarType};

use super::{Expr, ExprKind};

// FunctionExprent.FunctionType supplies the same operator metadata to both
// stack lifting and source writing. Primitive conversions also name their target.
macro_rules! function_types {
    ($( $op:ident($arity:literal, $operator:literal, $precedence:expr) $(=> $cast:ident)?; )+) => {
        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        pub enum FunctionType { $( $op, )+ }

        impl FunctionType {
            pub const fn arity(self) -> usize {
                match self { $( Self::$op => $arity, )+ }
            }

            pub(crate) fn java_operator(self) -> &'static str {
                match self { $( Self::$op => $operator, )+ }
            }

            pub(crate) fn java_precedence(self) -> i32 {
                match self { $( Self::$op => $precedence, )+ }
            }

            pub(crate) fn simple_cast_type(self) -> Option<VarType> {
                match self {
                    $( $( Self::$op => Some(VarType::$cast), )? )+
                    _ => None,
                }
            }
        }
    };
}

function_types! {
    Add(2, "+", 3);
    Sub(2, "-", 3);
    Mul(2, "*", 2);
    Div(2, "/", 2);
    And(2, "&", 7);
    Or(2, "|", 9);
    Xor(2, "^", 8);
    Rem(2, "%", 2);
    Shl(2, "<<", 4);
    Shr(2, ">>", 4);
    Ushr(2, ">>>", 4);

    BitNot(1, "~", 1);
    BoolNot(1, "!", 1);
    Neg(1, "-", 1);

    I2l(1, "", 1) => VARTYPE_LONG;
    I2f(1, "", 1) => VARTYPE_FLOAT;
    I2d(1, "", 1) => VARTYPE_DOUBLE;
    L2i(1, "", 1) => VARTYPE_INT;
    L2f(1, "", 1) => VARTYPE_FLOAT;
    L2d(1, "", 1) => VARTYPE_DOUBLE;
    F2i(1, "", 1) => VARTYPE_INT;
    F2l(1, "", 1) => VARTYPE_LONG;
    F2d(1, "", 1) => VARTYPE_DOUBLE;
    D2i(1, "", 1) => VARTYPE_INT;
    D2l(1, "", 1) => VARTYPE_LONG;
    D2f(1, "", 1) => VARTYPE_FLOAT;
    I2b(1, "", 1) => VARTYPE_BYTE;
    I2c(1, "", 1) => VARTYPE_CHAR;
    I2s(1, "", 1) => VARTYPE_SHORT;

    Cast(2, "", 1);
    InstanceOf(2, "instanceof", 6);
    ArrayLength(1, ".length", 0);
    Imm(1, "--", 1);
    Mmi(1, "--", 1);
    Ipp(1, "++", 1);
    Ppi(1, "++", 1);
    Ternary(3, "", 12);

    Lcmp(2, "__lcmp__", -1);
    Fcmpl(2, "__fcmpl__", -1);
    Fcmpg(2, "__fcmpg__", -1);
    Dcmpl(2, "__dcmpl__", -1);
    Dcmpg(2, "__dcmpg__", -1);
    Eq(2, "==", 6);
    Ne(2, "!=", 6);
    Lt(2, "<", 5);
    Ge(2, ">=", 5);
    Gt(2, ">", 5);
    Le(2, "<=", 5);
    BoolAnd(2, "&&", 10);
    BoolOr(2, "||", 11);
    StrConcat(2, "+", 3);
    Other(0, "??????", 999);
}

impl FunctionType {
    pub(crate) const fn is_arithmetic_binary(self) -> bool {
        use FunctionType::*;
        matches!(
            self,
            Add | Sub | Mul | Div | And | Or | Xor | Rem | Shl | Shr | Ushr
        )
    }

    pub const fn is_inc_dec(self) -> bool {
        matches!(self, Self::Imm | Self::Mmi | Self::Ipp | Self::Ppi)
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
            I2l | I2f | I2d | L2i | L2f | L2d | F2i | F2l | F2d | D2i | D2l | D2f | I2b | I2c
            | I2s => self.simple_cast_type().unwrap(),
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
