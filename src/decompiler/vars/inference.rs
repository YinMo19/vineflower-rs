// Copyright 2000-2017 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Bound inference over the direct graph after merging SSA phi versions.

use std::{collections::VecDeque, io};

use super::var_version_pair::VarVersionPair;
use crate::code::code_constants::ACC_STATIC;
use crate::decompiler::exps::{ConstantValue, Expr, ExprKind, FunctionType};
use crate::decompiler::ir::{ExprId, Ir, StatId, VarProcessorId};
use crate::decompiler::stats::StatementKind;
use crate::engine::method_timeout::checkpoint;
use crate::engine::Cx;
use crate::engine::counter_container::{CounterContainer, EXPRESSION_COUNTER};
use crate::structs::{StructClass, StructMember};
use crate::types::{CodeType, MethodDescriptor, TypeFamily, VarType};

/// `expressions` follows the direct graph's deep expression traversal, with
/// every occurrence of a shared expression retained.
pub(super) fn calculate(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    root: StatId,
    expressions: &[ExprId],
    owner: VarProcessorId,
    class: &StructClass,
    descriptor: &MethodDescriptor,
) -> io::Result<()> {
    initialize_variables(cx, root, owner, class, descriptor);

    reset_expression_types(&mut cx.ir, counters, expressions)?;

    'inference: loop {
        for &expr in expressions {
            checkpoint();
            if check_expression(cx, counters, owner, expr)? {
                continue 'inference;
            }
        }
        // The final lattice and variable checks in Java require optional validation.
        return Ok(());
    }
}

fn initialize_variables(
    cx: &mut Cx,
    root: StatId,
    owner: VarProcessorId,
    class: &StructClass,
    descriptor: &MethodDescriptor,
) {
    let is_static = root.method(&cx.ir).has_modifier(ACC_STATIC);
    if !is_static {
        let pair = VarVersionPair::new(0, 1);
        let class_type = VarType::with_value(CodeType::Object, 0, class.qualified_name.clone());
        cx.ir[owner].versions.lower.insert(pair, class_type.clone());
        cx.ir[owner].versions.upper.insert(pair, Some(class_type));
    }
    for (slot, parameter) in descriptor.parameter_slots(is_static) {
        let pair = VarVersionPair::new(slot, 1);
        cx.ir[owner].versions.lower.insert(pair, parameter.clone());
        cx.ir[owner]
            .versions
            .upper
            .insert(pair, Some(parameter.clone()));
    }

    let mut statements = VecDeque::from([root]);
    while let Some(stat) = statements.pop_front() {
        let catch = matches!(
            cx.ir[stat].kind,
            StatementKind::Catch { .. } | StatementKind::CatchAll { .. }
        );
        for expr in stat.implicitly_defined_vars(&cx.ir) {
            let ExprKind::Variable(var) = &cx.ir[expr].kind else {
                unreachable!("Implicit variable must be a variable expression");
            };
            let pair = VarVersionPair::new(var.index, 1);
            let ty = Expr::expr_type(cx, expr);
            cx.ir[owner].versions.lower.insert(pair, ty);
            if catch {
                let ty = Expr::expr_type(cx, expr);
                cx.ir[owner].versions.upper.insert(pair, Some(ty));
            }
        }
        statements.extend(cx.ir[stat].stats.iter().copied());
    }
}

fn reset_expression_types(
    ir: &mut Ir,
    counters: &mut CounterContainer,
    expressions: &[ExprId],
) -> io::Result<()> {
    for &expr in expressions {
        match &mut ir[expr].kind {
            ExprKind::Variable(var) => var.var_type = Some(VarType::VARTYPE_UNKNOWN),
            ExprKind::Constant {
                value,
                var_type,
                bool_permitted,
                ..
            } if var_type.type_family == TypeFamily::Integer => {
                *var_type = temporary_integer_type(counters, value, *bool_permitted)?;
            }
            _ => {}
        }
    }
    Ok(())
}

/// The temporary ConstExprent in upstream contributes an ID even though
/// only its type is retained.
fn temporary_integer_type(
    counters: &mut CounterContainer,
    value: &ConstantValue,
    bool_permitted: bool,
) -> io::Result<VarType> {
    let ConstantValue::Integer(value) = value else {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "Integer expression has a non-integer constant value",
        ));
    };
    counters.get_counter_and_increment(EXPRESSION_COUNTER);
    Ok(Expr::guess_int_type(*value, bool_permitted))
}

#[derive(Clone, Copy)]
enum Bound {
    Lower,
    Upper,
}

/// Return whether a lower bound changed enough to restart the traversal.
fn check_expression(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    owner: VarProcessorId,
    expr: ExprId,
) -> io::Result<bool> {
    if let ExprKind::Constant { var_type, .. } = &cx.ir[expr].kind
        && var_type.type_family.int_or_bool()
    {
        let pair = VarVersionPair::new(cx.ir[expr].id, -1);
        let var_type = var_type.clone();
        cx.ir[owner].versions.lower.entry(pair).or_insert(var_type);
    }

    let bounds = Expr::type_bounds(cx, expr)?;
    for (expr, ty) in bounds.upper {
        apply_bound(cx, counters, owner, expr, ty, Bound::Upper)?;
    }
    let mut restart = false;
    for (expr, ty) in bounds.lower {
        restart |= apply_bound(cx, counters, owner, expr, ty, Bound::Lower)?;
    }
    Ok(restart)
}

fn apply_bound(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    owner: VarProcessorId,
    expr: ExprId,
    mut ty: VarType,
    bound: Bound,
) -> io::Result<bool> {
    let pair = match &cx.ir[expr].kind {
        ExprKind::Constant {
            value, var_type, ..
        } => {
            if !ty.type_family.int_or_bool() || !var_type.type_family.int_or_bool() {
                return Ok(false);
            }
            if ty.type_family == TypeFamily::Integer {
                let minimum = temporary_integer_type(counters, value, false)?;
                if minimum.higher_in_lattice_than(cx, &ty) {
                    ty = minimum;
                }
            }
            VarVersionPair::new(cx.ir[expr].id, -1)
        }
        ExprKind::Variable(var) => VarVersionPair::new(var.index, var.version),
        ExprKind::Assignment { right, .. } => {
            return apply_bound(cx, counters, owner, *right, ty, bound);
        }
        ExprKind::Function { op, operands, .. } => {
            let start = match op {
                FunctionType::Ternary => 1,
                FunctionType::And | FunctionType::Or | FunctionType::Xor => 0,
                _ => return Ok(false),
            };
            let (left, right) = (operands[start], operands[start + 1]);
            let left_changed = apply_bound(cx, counters, owner, left, ty.clone(), bound)?;
            let right_changed = apply_bound(cx, counters, owner, right, ty, bound)?;
            return Ok(left_changed || right_changed);
        }
        ExprKind::Switch { var_type, .. } => {
            let promote = ty.type_family == TypeFamily::Integer
                && ty.higher_in_lattice_than(cx, var_type);
            if promote {
                let ExprKind::Switch { var_type, .. } = &mut cx.ir[expr].kind else {
                    unreachable!();
                };
                *var_type = ty;
            }
            return Ok(promote);
        }
        _ => return Ok(false),
    };

    match bound {
        Bound::Lower => raise_lower(cx, owner, expr, pair, ty),
        Bound::Upper => {
            apply_upper(cx, owner, pair, ty)?;
            Ok(false)
        }
    }
}

fn raise_lower(
    cx: &mut Cx,
    owner: VarProcessorId,
    expr: ExprId,
    pair: VarVersionPair,
    ty: VarType,
) -> io::Result<bool> {
    let current = cx.ir[owner].versions.lower.get(&pair);
    let next = match current {
        Some(current) if ty.type_family.is_lesser(current.type_family) => return Ok(false),
        Some(current) if ty.type_family == current.type_family => VarType::join(cx, current, &ty)
            .ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                "Assertion failed: Trying to raise the minimum type of disjoint variables!",
            )
        })?,
        _ => ty,
    };
    let restart = current.is_some_and(|current| {
        next.type_family.is_greater(current.type_family) || next.higher_in_lattice_than(cx, current)
    });
    if let ExprKind::Constant { var_type, .. } = &mut cx.ir[expr].kind {
        *var_type = next.clone();
    }
    cx.ir[owner].versions.lower.insert(pair, next);
    Ok(restart)
}

fn apply_upper(
    cx: &mut Cx,
    owner: VarProcessorId,
    pair: VarVersionPair,
    ty: VarType,
) -> io::Result<()> {
    let current = cx.ir[owner]
        .versions
        .upper
        .get(&pair)
        .and_then(Option::as_ref);
    let next = match current {
        Some(current) if ty.type_family == current.type_family => VarType::meet(cx, current, &ty)
            .ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                "Assertion failed: Trying to lower the maximum type of disjoint variables!",
            )
        })?,
        // Both a higher and a lower family replace the previous upper bound.
        _ => ty,
    };
    cx.ir[owner].versions.upper.insert(pair, Some(next));
    Ok(())
}
