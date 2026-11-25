// Copyright 2000-2020 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Expression rewrites from SecondaryFunctionsHelper.

use std::io;

use crate::decompiler::concat;
use crate::decompiler::exps::{Expr, ExprKind, FunctionType, Variable};
use crate::decompiler::ir::{ExprId, Ir};
use crate::decompiler::vars::var_version_pair::VarVersionPair;
use crate::engine::counter_container::VAR_COUNTER;
use crate::structs::consts::ConstantValue;
use crate::types::{CodeType, TypeFamily, VarType};

use super::Rewrite;

impl Rewrite<'_> {
    pub(super) fn identify_expression(
        &mut self,
        expr: ExprId,
        statement_level: bool,
    ) -> io::Result<Option<ExprId>> {
        if let Some(replacement) = self.before_children(expr, statement_level) {
            return Ok(Some(replacement));
        }

        let mut changed = false;
        'children: loop {
            let children = Expr::all_exprents(&self.cx.ir, expr, false, false);
            for child in children {
                if let Some(replacement) = self.identify_expression(child, false)? {
                    Expr::replace(&mut self.cx.ir, expr, child, replacement);
                    let offsets = self.cx.ir[child].bytecode.clone();
                    Expr::add_offsets(&mut self.cx.ir, replacement, offsets.as_ref());
                    changed = true;
                    continue 'children;
                }
            }
            break;
        }

        let replacement = match self.cx.ir[expr].kind {
            ExprKind::Function { .. } => self.after_function(expr),
            ExprKind::Assignment {
                left,
                right,
                compound: None,
            } => self.compound_assignment(expr, left, right),
            ExprKind::Invocation(_) => self.after_invocation(expr, statement_level)?,
            _ => None,
        };
        Ok(replacement.or(changed.then_some(expr)))
    }

    fn before_children(&mut self, expr: ExprId, statement_level: bool) -> Option<ExprId> {
        use FunctionType::*;
        let (op, operands) = function(&self.cx.ir, expr)?;
        match op {
            BoolNot => self.propagate_bool_not(expr),
            Eq | Ne | Lt | Ge | Gt | Le => self.numeric_comparison(op, operands[0], operands[1]),
            Ppi | Mmi if statement_level => {
                let next = if op == Ppi { Ipp } else { Imm };
                let replacement = self.build(next, [operands[0]], Some(expr));
                let ty = Expr::expr_type(self.cx, expr);
                let ExprKind::Function { implicit_type, .. } = &mut self.cx.ir[replacement].kind
                else {
                    unreachable!();
                };
                *implicit_type = Some(Box::new(ty));
                Some(replacement)
            }
            _ => None,
        }
    }

    fn after_function(&mut self, expr: ExprId) -> Option<ExprId> {
        use FunctionType::*;
        let (op, operands) = function(&self.cx.ir, expr).unwrap();
        match op {
            Xor => {
                for index in 0..2 {
                    let operand = operands[index];
                    let ty = Expr::expr_type(self.cx, operand);
                    if ty.ty != CodeType::Boolean
                        && let ExprKind::Constant { ref value, .. } = self.cx.ir[operand].kind
                    {
                        let value = match (ty.ty, value) {
                            (CodeType::Long, ConstantValue::Long(value)) => *value,
                            (_, ConstantValue::Integer(value)) if ty.ty != CodeType::Long => {
                                i64::from(*value)
                            }
                            _ => panic!("Invalid constant type for XOR"),
                        };
                        if value == -1 {
                            return Some(self.build(BitNot, [operands[1 - index]], Some(expr)));
                        }
                    }
                }
            }
            Eq | Ne if self.is_boolean(operands[0]) && self.is_boolean(operands[1]) => {
                for index in 0..2 {
                    if let Some(value) = int_constant(&self.cx.ir, operands[index]) {
                        let other = operands[1 - index];
                        return Some(if (op == Eq && value == 1) || (op == Ne && value == 0) {
                            other
                        } else {
                            self.build(BoolNot, [other], Some(expr))
                        });
                    }
                }
            }
            BoolNot => {
                if let Some(value) = int_constant(&self.cx.ir, operands[0]) {
                    let offsets = self.cx.ir[expr].bytecode.clone();
                    return Some(Expr::new(
                        &mut self.cx.ir,
                        self.counters,
                        Expr::constant(
                            VarType::VARTYPE_BOOLEAN,
                            ConstantValue::Integer(i32::from(value == 0)),
                            false,
                        ),
                        offsets,
                    ));
                }
            }
            Ternary => return self.ternary(expr, operands[0], operands[1], operands[2]),
            Lcmp | Fcmpl | Fcmpg | Dcmpl | Dcmpg => {
                return Some(self.expand_comparison(expr, operands[0], operands[1]));
            }
            I2b | I2c | I2s | I2l | I2f | I2d | L2f | L2d | F2d => {
                self.simplify_cast(expr, op, operands[0]);
            }
            Add | Sub | Mul | Div => {
                let left = operands[0];
                if let Some(left_type) = implicit_cast_type(&self.cx.ir, left)
                    && implicit_cast_type(&self.cx.ir, operands[1]) == Some(left_type)
                {
                    set_cast(&mut self.cx.ir, left, true);
                }
            }
            Shl | Shr | Ushr => {
                let left = operands[0];
                if implicit_cast_type(&self.cx.ir, left).is_some() {
                    set_cast(&mut self.cx.ir, left, true);
                }
            }
            _ => {}
        }
        None
    }

    fn propagate_bool_not(&mut self, expr: ExprId) -> Option<ExprId> {
        use FunctionType::*;
        let (BoolNot, operands) = function(&self.cx.ir, expr)? else {
            return None;
        };
        let parameter = operands[0];
        let (op, operands) = function(&self.cx.ir, parameter)?;
        if op != BoolNot
            && Expr::children(&self.cx.ir, parameter)
                .chain([parameter])
                .any(|child| {
                    matches!(
                        function(&self.cx.ir, child),
                        Some((InstanceOf, operands)) if operands.len() > 2
                    )
                })
        {
            return None;
        }
        match op {
            BoolNot => {
                let inner = operands[0];
                return self.propagate_bool_not(inner).or(Some(inner));
            }
            Ternary => {
                let (yes, no) = (operands[1], operands[2]);
                let yes = self.build(BoolNot, [yes], None);
                let no = self.build(BoolNot, [no], None);
                let yes = self.propagate_bool_not(yes).unwrap_or(yes);
                let no = self.propagate_bool_not(no).unwrap_or(no);
                let ExprKind::Function { operands, .. } = &mut self.cx.ir[parameter].kind else {
                    unreachable!();
                };
                operands[1] = yes;
                operands[2] = no;
                return Some(parameter);
            }
            BoolAnd | BoolOr => {
                for index in 0..operands.len() {
                    let (_, operands) = function(&self.cx.ir, parameter).unwrap();
                    let operand = operands[index];
                    let negated = self.build(BoolNot, [operand], Some(operand));
                    let negated = self.propagate_bool_not(negated).unwrap_or(negated);
                    let ExprKind::Function { operands, .. } = &mut self.cx.ir[parameter].kind
                    else {
                        unreachable!();
                    };
                    operands[index] = negated;
                }
            }
            Eq | Ne => {}
            Lt | Ge | Gt | Le => {
                let left = Expr::expr_type(self.cx, operands[0]);
                let right = Expr::expr_type(self.cx, operands[1]);
                let common = VarType::join(self.cx, &left, &right)?;
                if matches!(common.ty, CodeType::Float | CodeType::Double) {
                    return None;
                }
            }
            _ => return None,
        }
        let ExprKind::Function { op: actual, .. } = &mut self.cx.ir[parameter].kind else {
            unreachable!();
        };
        *actual = opposite(op);
        Some(parameter)
    }

    fn ternary(&mut self, expr: ExprId, test: ExprId, yes: ExprId, no: ExprId) -> Option<ExprId> {
        use FunctionType::*;
        let boolean_constant = |value: ExprId| {
            (matches!(self.cx.ir[value].kind, ExprKind::Constant { .. }) && self.is_boolean(value))
                .then(|| int_constant(&self.cx.ir, value).unwrap() != 0)
        };
        let yes_const = boolean_constant(yes);
        let no_const = boolean_constant(no);
        match (yes_const, no_const) {
            (Some(true), Some(false)) => return Some(test),
            (Some(false), Some(true)) => return Some(self.build(BoolNot, [test], Some(expr))),
            _ => {}
        }
        if !self.force_ternary && !self.cx.options.ternary_constant_simplification {
            return None;
        }
        let (op, test, branch) = match (yes_const, no_const) {
            (Some(true), _) => (BoolOr, test, no),
            (Some(false), _) => (BoolAnd, self.build(BoolNot, [test], Some(expr)), no),
            (_, Some(true)) => (BoolOr, self.build(BoolNot, [test], Some(expr)), yes),
            (_, Some(false)) => (BoolAnd, test, yes),
            _ if self.is_boolean(yes) && Expr::equals(self.cx, yes, test) => (BoolOr, test, no),
            _ if self.is_boolean(no) && Expr::equals(self.cx, no, test) => (BoolAnd, test, yes),
            _ => return None,
        };
        Some(self.build(op, [test, branch], Some(expr)))
    }

    fn numeric_comparison(
        &mut self,
        outer: FunctionType,
        left: ExprId,
        right: ExprId,
    ) -> Option<ExprId> {
        use FunctionType::*;
        let (comparison, constant) = if matches!(self.cx.ir[left].kind, ExprKind::Constant { .. }) {
            (right, left)
        } else {
            (left, right)
        };
        let (inner, operands) = function(&self.cx.ir, comparison)?;
        if !matches!(inner, Lcmp | Fcmpg | Fcmpl | Dcmpg | Dcmpl) {
            return None;
        }
        let value = int_constant(&self.cx.ir, constant)?;
        let targets = match outer {
            Eq => [Some(Lt), Some(Eq), Some(Gt)],
            Ne => [Some(Ge), Some(Ne), Some(Le)],
            Gt => [Some(Ge), Some(Gt), None],
            Ge => [None, Some(Ge), Some(Gt)],
            Lt => [None, Some(Lt), Some(Le)],
            Le => [Some(Lt), Some(Le), None],
            _ => unreachable!(),
        };
        let index = usize::try_from(value.wrapping_add(1)).ok()?;
        let target = (*targets.get(index)?)?;
        let operands = [operands[0], operands[1]];
        let true_for_nan =
            inner != Lcmp && matches!(inner, Dcmpl | Fcmpl) == matches!(target, Lt | Le);
        if true_for_nan {
            let inner = self.build(opposite(target), operands, Some(comparison));
            Some(self.build(BoolNot, [inner], Some(comparison)))
        } else {
            Some(self.build(target, operands, Some(comparison)))
        }
    }

    fn expand_comparison(&mut self, expr: ExprId, left: ExprId, right: ExprId) -> ExprId {
        use FunctionType::*;
        let slot = self.counters.get_counter_and_increment(VAR_COUNTER);
        let ty = Expr::expr_type(self.cx, left);
        let zero = match ty.ty {
            CodeType::Int => ConstantValue::Integer(0),
            CodeType::Long => ConstantValue::Long(0),
            CodeType::Double => ConstantValue::Double(0.0),
            CodeType::Float => ConstantValue::Float(0.0),
            _ => panic!("Invalid type for a comparison temporary"),
        };

        let read = self.temporary(slot, ty.clone());
        let against = self.constant(ty.clone(), zero.clone());
        let less = self.build(Lt, [read, against], None);
        let minus_one = self.constant(VarType::VARTYPE_INT, ConstantValue::Integer(-1));
        let one = self.constant(VarType::VARTYPE_INT, ConstantValue::Integer(1));
        let when_nonzero = self.build(Ternary, [less, minus_one, one], None);

        let write = self.temporary(slot, ty.clone());
        let difference = self.build(Sub, [left, right], None);
        let assignment = Expr::new(
            &mut self.cx.ir,
            self.counters,
            ExprKind::Assignment {
                left: write,
                right: difference,
                compound: None,
            },
            None,
        );
        let against = self.constant(ty.clone(), zero);
        let equal = self.build(Eq, [assignment, against], None);
        let versions = &mut self.cx.ir[self.owner];
        if versions.initialized {
            versions.lower.insert(VarVersionPair::new(slot, 0), ty);
        }
        let zero = self.constant(VarType::VARTYPE_INT, ConstantValue::Integer(0));
        self.build(Ternary, [equal, zero, when_nonzero], Some(expr))
    }

    fn simplify_cast(&mut self, expr: ExprId, op: FunctionType, operand: ExprId) {
        use FunctionType::*;
        if matches!(op, I2b | I2c | I2s)
            && function(&self.cx.ir, operand)
                .is_some_and(|(inner, _)| inner.simple_cast_type() == Some(VarType::VARTYPE_INT))
        {
            set_cast(&mut self.cx.ir, operand, false);
            return;
        }
        let source = Expr::expr_type(self.cx, operand);
        let target = op.simple_cast_type().unwrap();
        let widening = if target.type_family == TypeFamily::Integer {
            target.higher_in_lattice_than(self.cx, &source)
        } else {
            target.type_family.is_greater(source.type_family)
        };
        if widening {
            set_cast(&mut self.cx.ir, expr, false);
        }
    }

    fn compound_assignment(&mut self, expr: ExprId, left: ExprId, right: ExprId) -> Option<ExprId> {
        use FunctionType::*;
        let (mut op, mut operands) = function(&self.cx.ir, right)?;
        if !simple_assignment_target(&self.cx.ir, left, None) {
            return None;
        }
        let cast_type = op.simple_cast_type();
        if cast_type.is_some() {
            (op, operands) = function(&self.cx.ir, operands[0])?;
        }
        let value = match op {
            Add | And | Or | Xor if Expr::equals(self.cx, left, operands[1]) => operands[0],
            Add | And | Or | Xor | Sub | Mul | Div | Rem | Shl | Shr | Ushr
                if Expr::equals(self.cx, left, operands[0]) =>
            {
                operands[1]
            }
            _ => return None,
        };
        if cast_type.is_some_and(|cast| cast != Expr::expr_type(self.cx, value))
            || !simple_assignment_target(&self.cx.ir, left, Some(value))
        {
            return None;
        }
        let ExprKind::Assignment {
            right, compound, ..
        } = &mut self.cx.ir[expr].kind
        else {
            unreachable!();
        };
        *right = value;
        *compound = Some(op);
        Some(expr)
    }

    fn after_invocation(
        &mut self,
        expr: ExprId,
        statement_level: bool,
    ) -> io::Result<Option<ExprId>> {
        let ExprKind::Invocation(invoke) = &self.cx.ir[expr].kind else {
            unreachable!();
        };
        if invoke.is_boxing_call(self.cx) {
            let parameter = invoke.parameters[0];
            if implicit_cast_type(&self.cx.ir, parameter).is_some() {
                set_cast(&mut self.cx.ir, parameter, true);
            }
            if statement_level {
                let ExprKind::Invocation(invoke) = &mut self.cx.ir[expr].kind else {
                    unreachable!();
                };
                invoke.force_boxing = true;
            }
        }
        if statement_level {
            return Ok(None);
        }
        let result = concat::contract(self.cx, self.counters, self.root, expr)?;
        Ok((!Expr::equals(self.cx, expr, result)).then_some(result))
    }

    fn is_boolean(&self, expr: ExprId) -> bool {
        Expr::expr_type(self.cx, expr).ty == CodeType::Boolean
    }

    fn temporary(&mut self, slot: i32, ty: VarType) -> ExprId {
        let kind = ExprKind::Variable(Variable::in_method(slot, ty, self.owner));
        Expr::new(&mut self.cx.ir, self.counters, kind, None)
    }

    fn constant(&mut self, ty: VarType, value: ConstantValue) -> ExprId {
        let kind = Expr::constant(ty, value, false);
        Expr::new(&mut self.cx.ir, self.counters, kind, None)
    }

    fn build(
        &mut self,
        op: FunctionType,
        operands: impl Into<Vec<ExprId>>,
        source: Option<ExprId>,
    ) -> ExprId {
        let offsets = source.and_then(|source| self.cx.ir[source].bytecode.clone());
        Expr::function(&mut self.cx.ir, self.counters, op, operands.into(), offsets)
    }
}

fn function(ir: &Ir, expr: ExprId) -> Option<(FunctionType, &[ExprId])> {
    match &ir[expr].kind {
        ExprKind::Function { op, operands, .. } => Some((*op, operands)),
        _ => None,
    }
}

fn int_constant(ir: &Ir, expr: ExprId) -> Option<i32> {
    match &ir[expr].kind {
        ExprKind::Constant {
            value: ConstantValue::Integer(value),
            ..
        } => Some(*value),
        ExprKind::Constant { .. } => panic!("Expected a boxed integer constant"),
        _ => None,
    }
}

fn opposite(op: FunctionType) -> FunctionType {
    use FunctionType::*;
    match op {
        Eq => Ne,
        Ne => Eq,
        Lt => Ge,
        Ge => Lt,
        Gt => Le,
        Le => Gt,
        BoolAnd => BoolOr,
        BoolOr => BoolAnd,
        _ => unreachable!("Function has no opposite comparison"),
    }
}

fn implicit_cast_type(ir: &Ir, expr: ExprId) -> Option<VarType> {
    if let ExprKind::Function {
        op,
        needs_cast: false,
        ..
    } = ir[expr].kind
    {
        op.simple_cast_type()
    } else {
        None
    }
}

fn set_cast(ir: &mut Ir, expr: ExprId, needed: bool) {
    let ExprKind::Function { needs_cast, .. } = &mut ir[expr].kind else {
        unreachable!("Only a function can carry a cast");
    };
    *needs_cast = needed;
}

fn simple_assignment_target(ir: &Ir, target: ExprId, value: Option<ExprId>) -> bool {
    let single = |expr: ExprId| {
        matches!(
            ir[expr].kind,
            ExprKind::Variable(_) | ExprKind::Constant { .. }
        )
    };
    match ir[target].kind {
        ExprKind::Array { array, index, .. } => single(array) && single(index),
        ExprKind::Field(_) => {
            value.is_none_or(|expr| Expr::usage(ir, expr) & Expr::SIDE_EFFECTS_FREE != 0)
        }
        _ => single(target),
    }
}
