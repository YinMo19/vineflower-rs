//! Install the labels described by SwitchBootstraps arguments.

use std::io;

use super::{PatternSwitch, constant, int_constant, invalid, switch, switch_mut};
use crate::code::code_constants::{CONSTANT_CLASS, CONSTANT_INTEGER, CONSTANT_STRING};
use crate::decompiler::exps::{ConstantValue, Expr, ExprKind, Field, FunctionType, Variable};
use crate::decompiler::ir::{ExprId, Ir, StatId, VarProcessorId};
use crate::engine::Cx;
use crate::engine::counter_container::{CounterContainer, VAR_COUNTER};
use crate::structs::consts::PooledConstant;
use crate::types::{CodeType, FieldDescriptor, TypeFamily, VarType};

pub(super) fn install_labels(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    pattern: &PatternSwitch,
    variables: VarProcessorId,
    arguments: &[Option<PooledConstant>],
) -> io::Result<()> {
    for (ordinal, argument) in arguments.iter().enumerate() {
        let mut index = bootstrap_case(cx, pattern.stat, ordinal);
        let Some(PooledConstant::Primitive(primitive)) = argument else {
            continue;
        };
        let value = match primitive.ty {
            CONSTANT_INTEGER => {
                let ConstantValue::Integer(value) = primitive.value else {
                    unreachable!("Integer bootstrap entry has noninteger data");
                };
                Expr::new_int_constant(&mut cx.ir, counters, value, false)
            }
            CONSTANT_STRING => {
                let label = if pattern.is_enum {
                    let name = Expr::expr_type(cx, pattern.selector)
                        .value
                        .ok_or_else(|| invalid("Enum switch has no selector type"))?;
                    let descriptor = FieldDescriptor::parse_descriptor(&format!("L{name};"));
                    Expr::new(
                        &mut cx.ir,
                        counters,
                        ExprKind::Field(Box::new(Field {
                            name: primitive.get_string().clone(),
                            classname: Some(name),
                            instance: None,
                            descriptor,
                            force_qualified: false,
                            was_condy: false,
                        })),
                        None,
                    )
                } else {
                    constant(
                        &mut cx.ir,
                        counters,
                        VarType::VARTYPE_STRING,
                        primitive.value.clone(),
                    )
                };
                index = string_case(&cx.ir, pattern.stat, ordinal as i32)?;
                label
            }
            CONSTANT_CLASS => {
                let values = &switch(&cx.ir, pattern.stat)
                    .cases
                    .get(index)
                    .ok_or_else(|| invalid("Class bootstrap argument has no switch case"))?
                    .values;
                if !values.iter().all(|label| {
                    label.is_some_and(|expr| matches!(cx.ir[expr].kind, ExprKind::Constant { .. }))
                }) {
                    continue;
                }
                let cast_type =
                    VarType::with_value(CodeType::Object, 0, primitive.get_string().clone());
                let ty = constant(&mut cx.ir, counters, cast_type.clone(), ConstantValue::Null);
                let variable = Variable::in_method(
                    counters.get_counter_and_increment(VAR_COUNTER),
                    cast_type,
                    variables,
                );
                let variable = Expr::new(&mut cx.ir, counters, ExprKind::Variable(variable), None);
                Expr::function(
                    &mut cx.ir,
                    counters,
                    FunctionType::InstanceOf,
                    vec![pattern.selector, ty, variable],
                    None,
                )
            }
            _ => return Err(invalid("Unexpected primitive switch bootstrap argument")),
        };
        replace_index(&mut cx.ir, pattern.stat, index, ordinal as i32, value)?;
    }
    Ok(())
}

fn bootstrap_case(cx: &Cx, stat: StatId, ordinal: usize) -> usize {
    let cases = &switch(&cx.ir, stat).cases;
    let mut index = ordinal;
    for case in cases {
        if case
            .values
            .first()
            .copied()
            .flatten()
            .and_then(|expr| int_constant(&cx.ir, expr))
            == Some(ordinal as i32)
        {
            // List.indexOf uses structural equality and may find an earlier
            // case after an integer bootstrap label has already been installed.
            index = cases
                .iter()
                .position(|other| same_values(cx, &case.values, &other.values))
                .expect("Case list cannot find its own values");
        }
    }
    index
}

fn same_values(cx: &Cx, left: &[Option<ExprId>], right: &[Option<ExprId>]) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|(&left, &right)| match (left, right) {
                (Some(left), Some(right)) => Expr::equals(cx, left, right),
                (None, None) => true,
                _ => false,
            })
}

fn string_case(ir: &Ir, stat: StatId, ordinal: i32) -> io::Result<usize> {
    switch(ir, stat)
        .cases
        .iter()
        .position(|case| {
            case.values
                .iter()
                .flatten()
                .any(|&expr| int_constant(ir, expr) == Some(ordinal))
        })
        .ok_or_else(|| invalid("Unexpected case in switch pattern matching"))
}

fn replace_index(
    ir: &mut Ir,
    stat: StatId,
    case: usize,
    ordinal: i32,
    value: ExprId,
) -> io::Result<()> {
    let labels = &mut switch_mut(ir, stat)
        .cases
        .get_mut(case)
        .ok_or_else(|| invalid("Switch bootstrap argument has no case"))?
        .values;
    let mut values = std::mem::take(labels);
    for label in &mut values {
        if let Some(expr) = *label
            && matches!(&ir[expr].kind, ExprKind::Constant { var_type, .. }
                if var_type.type_family == TypeFamily::Integer)
            && int_constant(ir, expr) == Some(ordinal)
        {
            *label = Some(value);
        }
    }
    switch_mut(ir, stat).cases[case].values = values;
    Ok(())
}
