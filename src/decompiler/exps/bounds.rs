// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Type constraints emitted by `Exprent.checkExprTypeBounds`.

use crate::decompiler::ir::ExprId;
use crate::decompiler::stats::StatementKind;
use crate::engine::Cx;
use crate::types::{CodeType, VarType};

use super::{ConstantValue, ExitType, Expr, ExprKind, FunctionType, Invocation, SwitchCaseValues};

#[derive(Default)]
pub(crate) struct ExprBounds {
    pub upper: Vec<(ExprId, VarType)>,
    pub lower: Vec<(ExprId, VarType)>,
}

impl ExprBounds {
    fn restrict(&mut self, expr: ExprId, lower: VarType, upper: VarType) {
        self.lower.push((expr, lower));
        self.upper.push((expr, upper));
    }

    fn restrict_to_family(&mut self, expr: ExprId, upper: VarType) {
        self.restrict(expr, VarType::find_family_bottom(upper.type_family), upper);
    }
}

impl Expr {
    pub(crate) fn type_bounds(cx: &Cx, expr: ExprId) -> ExprBounds {
        let mut bounds = ExprBounds::default();
        match &cx.ir[expr].kind {
            ExprKind::Variable(var) => {
                if let Some(lvt) = &var.lvt {
                    bounds.lower.push((expr, lvt.get_var_type()));
                }
            }
            ExprKind::Assignment { left, right, .. } => {
                bounds.lower.push(assignment_bound(cx, *left, *right));
            }
            ExprKind::Array { index, .. } => {
                bounds.restrict(*index, VarType::VARTYPE_BYTECHAR, VarType::VARTYPE_INT);
            }
            ExprKind::Exit {
                kind: ExitType::Return,
                value,
                return_type,
                ..
            } => {
                let ty = return_type.as_ref().expect("Missing return type");
                if ty.ty != CodeType::Void {
                    bounds.restrict_to_family(value.expect("Missing return value"), ty.clone());
                }
            }
            ExprKind::Invocation(invoke) => invoke_bounds(cx, invoke, &mut bounds),
            ExprKind::New {
                new_type,
                dimensions,
                array_elements,
                constructor,
                ..
            } => {
                if new_type.array_dim != 0 {
                    for &dimension in dimensions {
                        bounds.restrict(dimension, VarType::VARTYPE_BYTECHAR, VarType::VARTYPE_INT);
                    }
                    if new_type.array_dim == 1 {
                        let element_type = new_type.decrease_array_dim();
                        for &element in array_elements {
                            bounds.restrict_to_family(element, element_type.clone());
                        }
                    }
                } else if let Some(constructor) = constructor {
                    let ExprKind::Invocation(invoke) = &cx.ir[*constructor].kind else {
                        unreachable!("New expression constructor must be an invocation");
                    };
                    invoke_bounds(cx, invoke, &mut bounds);
                }
            }
            ExprKind::SwitchHead { value, case_values } => {
                switch_bounds(cx, *value, case_values.as_ref(), &mut bounds);
            }
            ExprKind::Function {
                op,
                operands,
                implicit_type,
            } => {
                function_bounds(cx, *op, operands, implicit_type.as_deref(), &mut bounds);
            }
            ExprKind::Constant { .. }
            | ExprKind::Field(_)
            | ExprKind::Exit { .. }
            | ExprKind::Monitor { .. }
            | ExprKind::If { .. } => {}
        }
        bounds
    }
}

fn assignment_bound(cx: &Cx, left: ExprId, right: ExprId) -> (ExprId, VarType) {
    use std::cmp::Ordering;

    let left_type = Expr::expr_type(cx, left);
    let mut right_type = Expr::expr_type(cx, right);
    match left_type.type_family.cmp(&right_type.type_family) {
        Ordering::Greater => (right, VarType::find_family_bottom(left_type.type_family)),
        Ordering::Less => (left, right_type),
        Ordering::Equal => {
            // The ternary's Java expression type promotes integer constants.
            // An assignment may still target a narrower integer type.
            if right_type == VarType::VARTYPE_INT
                && matches!(
                    cx.ir[right].kind,
                    ExprKind::Function {
                        op: FunctionType::Ternary,
                        ..
                    }
                )
            {
                right_type = VarType::VARTYPE_BYTECHAR;
            }
            (
                left,
                VarType::join(cx, &left_type, &right_type).expect("Null assignment type bound"),
            )
        }
    }
}

fn invoke_bounds(cx: &Cx, invoke: &Invocation, bounds: &mut ExprBounds) {
    if let Some(instance) = invoke.instance {
        bounds.restrict_to_family(instance, Expr::expr_type(cx, instance));
    }
    for (index, &parameter) in invoke.parameters.iter().enumerate() {
        bounds.restrict_to_family(parameter, invoke.descriptor.params[index].clone());
    }
}

fn switch_bounds(
    cx: &Cx,
    selector: ExprId,
    cases: Option<&SwitchCaseValues>,
    bounds: &mut ExprBounds,
) {
    bounds.restrict(selector, VarType::VARTYPE_BYTECHAR, VarType::VARTYPE_INT);
    let mut selector_type = Some(Expr::expr_type(cx, selector));
    let mut check_cases = |labels: &[Option<ExprId>]| {
        for &label in labels.iter().flatten() {
            let type_expr = match &cx.ir[label].kind {
                ExprKind::Function { operands, .. } if operands.len() == 3 => operands[1],
                _ => label,
            };
            let case_type = Expr::expr_type(cx, type_expr);
            let current = selector_type
                .as_ref()
                .expect("Invalid switch case set for selector");
            if case_type == *current
                || current
                    .unboxing_type()
                    .is_some_and(|unboxed| unboxed.higher_equal_in_lattice_than(cx, &case_type))
            {
                continue;
            }
            selector_type = VarType::join(cx, &case_type, current);
            if let Some(ty) = &selector_type {
                bounds.lower.push((selector, ty.clone()));
            }
        }
    };
    match cases {
        Some(SwitchCaseValues::Statement(stat)) => {
            let StatementKind::Switch(switch) = &cx.ir[*stat].kind else {
                unreachable!("Switch header case values belong to a switch statement");
            };
            for case in &switch.cases {
                check_cases(&case.values);
            }
        }
        Some(SwitchCaseValues::Copied(cases)) => {
            for case in cases {
                check_cases(case);
            }
        }
        None => {}
    }
}

fn function_bounds(
    cx: &Cx,
    op: FunctionType,
    operands: &[ExprId],
    implicit_type: Option<&VarType>,
    bounds: &mut ExprBounds,
) {
    use FunctionType::*;

    let first = operands[0];
    let first_type = Expr::expr_type(cx, first);
    let second_type = operands.get(1).map(|&second| Expr::expr_type(cx, second));
    match op {
        Ternary => {
            let supertype = op.expr_type(cx, operands, implicit_type);
            let bottom = VarType::find_family_bottom(supertype.type_family);
            bounds.restrict(first, VarType::VARTYPE_BOOLEAN, VarType::VARTYPE_BOOLEAN);
            bounds.restrict(operands[1], bottom.clone(), supertype.clone());
            bounds.restrict(operands[2], bottom, supertype);
        }
        I2l | I2f | I2d | I2b | I2c | I2s => {
            bounds.restrict(first, VarType::VARTYPE_BYTECHAR, VarType::VARTYPE_INT);
        }
        Imm | Ipp | Mmi | Ppi => {
            let ty = implicit_type.expect("Missing increment or decrement expression type");
            bounds.restrict(first, ty.clone(), ty.clone());
        }
        Add | Sub | Mul | Div | Rem | Shl | Shr | Ushr | Lt | Ge | Gt | Le => {
            bounds.lower.push((operands[1], VarType::VARTYPE_BYTECHAR));
            bounds.lower.push((first, VarType::VARTYPE_BYTECHAR));
        }
        BitNot | Neg => bounds.lower.push((first, VarType::VARTYPE_BYTECHAR)),
        And | Or | Xor | Eq | Ne => {
            let second = operands[1];
            let second_type = second_type.unwrap();
            if first_type.ty == CodeType::Boolean {
                if second_type.higher_in_lattice_than(cx, &first_type) {
                    bounds.lower.push((first, VarType::VARTYPE_BYTECHAR));
                } else if invalid_boolean_constant(cx, first)
                    || invalid_boolean_constant(cx, second)
                {
                    bounds.lower.push((first, VarType::VARTYPE_BYTECHAR));
                    bounds.lower.push((second, VarType::VARTYPE_BYTECHAR));
                }
            } else if second_type.ty == CodeType::Boolean
                && first_type.higher_in_lattice_than(cx, &second_type)
            {
                bounds.lower.push((second, VarType::VARTYPE_BYTECHAR));
            }
        }
        InstanceOf => {
            if let Some(&binding) = operands.get(2)
                && matches!(cx.ir[binding].kind, ExprKind::Variable(_))
            {
                bounds.lower.push((binding, second_type.unwrap()));
            }
        }
        Cast => bounds.restrict_to_family(first, second_type.unwrap()),
        BoolNot | BoolAnd | BoolOr | L2i | L2f | L2d | F2i | F2l | F2d | D2i | D2l | D2f
        | ArrayLength | Lcmp | Fcmpl | Fcmpg | Dcmpl | Dcmpg => {}
    }
}

fn invalid_boolean_constant(cx: &Cx, expr: ExprId) -> bool {
    let ExprKind::Constant {
        value, var_type, ..
    } = &cx.ir[expr].kind
    else {
        return false;
    };
    if !matches!(
        var_type.ty,
        CodeType::Boolean
            | CodeType::Char
            | CodeType::Byte
            | CodeType::Bytechar
            | CodeType::Short
            | CodeType::Shortchar
            | CodeType::Int
    ) {
        return true;
    }
    let ConstantValue::Integer(value) = *value else {
        unreachable!("Boolean value requires an integer constant");
    };
    value != 0 && (value != 1 || !cx.options.boolean_as_int)
}
