//! Fold consecutive element writes into array allocations.

use rustc_hash::FxHashMap;

use super::variable;
use crate::decompiler::exps::{ConstantValue, Expr, ExprKind};
use crate::decompiler::ir::{ExprId, ExprListId, Ir};
use crate::engine::Cx;
use crate::engine::counter_container::CounterContainer;
use crate::types::{CodeType, VarType};

pub(super) fn initializer(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    list: ExprListId,
    index: usize,
    current: ExprId,
) -> usize {
    let Some((array, allocation)) = cx.ir[current].as_assignment() else {
        return 0;
    };
    let Some(var) = variable(&cx.ir, array) else {
        return 0;
    };
    let ExprKind::New {
        new_type,
        dimensions,
        array_elements,
        ..
    } = &cx.ir[allocation].kind
    else {
        return 0;
    };
    if Expr::expr_type(cx, allocation).array_dim <= 0 || !array_elements.is_empty() {
        return 0;
    }
    let [dimension] = dimensions.as_ref() else {
        return 0;
    };
    let Some(size) = int_constant(&cx.ir, *dimension) else {
        return 0;
    };
    if size <= 0 {
        return 0;
    }

    let mut values = FxHashMap::default();
    let mut last_impure = -1;
    for &expr in cx.ir[list].iter().skip(index + 1).take(size as usize) {
        let Some((slot, value)) = array_write(cx, expr, array) else {
            break;
        };
        if slot >= size || values.contains_key(&slot) {
            break;
        }
        if Expr::usage(&cx.ir, value) & Expr::SIDE_EFFECTS_FREE == 0 {
            if slot < last_impure {
                break;
            }
            last_impure = slot;
        }
        if Expr::contains(cx, value, array) {
            break;
        }
        values.insert(slot, value);
    }

    let coverage = values.len() as f64 / f64::from(size);
    if !((var.stack && coverage > 0.0)
        || (size <= 7 && coverage >= 0.3)
        || (size > 7 && coverage >= 0.7))
    {
        return 0;
    }
    let dims = new_type.array_dim;
    let element_type = new_type.decrease_array_dim();
    let default = default_array_value(cx, counters, &element_type);
    let mut filled: Box<[_]> = (0..size)
        .map(|_| Expr::copy(cx, counters, default))
        .collect();
    for (&slot, &value) in &values {
        filled[slot as usize] = value;
        mark_nested_initializer(&mut cx.ir, value, dims);
    }
    let ExprKind::New { array_elements, .. } = &mut cx.ir[allocation].kind else {
        unreachable!()
    };
    *array_elements = filled;
    values.len()
}

pub(super) fn add_element(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    first: ExprId,
    second: ExprId,
) -> bool {
    let Some((array, allocation)) = cx.ir[first].as_assignment() else {
        return false;
    };
    let ExprKind::New {
        new_type,
        array_elements,
        ..
    } = &cx.ir[allocation].kind
    else {
        return false;
    };
    if array_elements.is_empty() || variable(&cx.ir, array).is_none() {
        return false;
    }
    let Some((slot, value)) = array_write(cx, second, array) else {
        return false;
    };
    if slot >= array_elements.len() as i32 {
        return false;
    }
    let slot = slot as usize;
    let previous = array_elements[slot];
    if !matches!(cx.ir[previous].kind, ExprKind::Constant { .. }) {
        return false;
    }
    let dims = new_type.array_dim;
    let element_type = new_type.decrease_array_dim();
    let default = default_array_value(cx, counters, &element_type);
    if !Expr::equals(cx, previous, default) {
        return false;
    }
    let ExprKind::New { array_elements, .. } = &cx.ir[allocation].kind else {
        unreachable!()
    };
    if Expr::usage(&cx.ir, value) & Expr::SIDE_EFFECTS_FREE == 0
        && array_elements[slot + 1..]
            .iter()
            .any(|&later| Expr::usage(&cx.ir, later) & Expr::SIDE_EFFECTS_FREE == 0)
    {
        return false;
    }
    if Expr::contains(cx, value, array) {
        return false;
    }
    let ExprKind::New { array_elements, .. } = &mut cx.ir[allocation].kind else {
        unreachable!()
    };
    array_elements[slot] = value;
    mark_nested_initializer(&mut cx.ir, value, dims);
    true
}

fn array_write(cx: &Cx, expr: ExprId, target: ExprId) -> Option<(i32, ExprId)> {
    let (left, value) = cx.ir[expr].as_assignment()?;
    let ExprKind::Array { array, index, .. } = cx.ir[left].kind else {
        return None;
    };
    if variable(&cx.ir, array).is_some() && Expr::equals(cx, target, array) {
        Some((int_constant(&cx.ir, index)?, value))
    } else {
        None
    }
}

fn int_constant(ir: &Ir, expr: ExprId) -> Option<i32> {
    match ir[expr].kind {
        ExprKind::Constant {
            value: ConstantValue::Integer(value),
            ..
        } => Some(value),
        _ => None,
    }
}

fn mark_nested_initializer(ir: &mut Ir, child: ExprId, dims: i32) {
    if dims > 1
        && let ExprKind::New {
            array_elements,
            direct_array_init,
            ..
        } = &mut ir[child].kind
        && !array_elements.is_empty()
    {
        *direct_array_init = true;
    }
}

fn default_array_value(cx: &mut Cx, counters: &mut CounterContainer, ty: &VarType) -> ExprId {
    let kind = if ty.ty == CodeType::Object || ty.array_dim > 0 {
        Expr::constant(VarType::VARTYPE_NULL, ConstantValue::Null, false)
    } else {
        match ty.ty {
            CodeType::Float => {
                Expr::constant(VarType::VARTYPE_FLOAT, ConstantValue::Float(0.0), false)
            }
            CodeType::Long => Expr::constant(VarType::VARTYPE_LONG, ConstantValue::Long(0), false),
            CodeType::Double => {
                Expr::constant(VarType::VARTYPE_DOUBLE, ConstantValue::Double(0.0), false)
            }
            _ => Expr::int_constant(0, true),
        }
    };
    Expr::new(&mut cx.ir, counters, kind, None)
}
