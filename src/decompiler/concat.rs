//! Recover the builder and invokedynamic forms of string concatenation.

use std::{io, mem};

use crate::code::code_constants::CONSTANT_STRING;
use crate::decompiler::exps::{
    BytecodeOffsets, ConstantValue, Expr, ExprKind, FunctionType, Invocation,
};
use crate::decompiler::ir::{ExprId, Ir, StatId};
use crate::engine::{Cx, counter_container::CounterContainer};
use crate::structs::consts::PooledConstant;
use crate::types::{CodeType, VarType};
use crate::util::java_str::JavaString;

const STRING_BUILDER: &str = "java/lang/StringBuilder";
const STRING_BUFFER: &str = "java/lang/StringBuffer";
const STRING: &str = "java/lang/String";
const TAG_ARG: u16 = 1;
const TAG_CONST: u16 = 2;

pub(crate) fn simplify(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    root: StatId,
) -> io::Result<()> {
    let cx = &mut *cx.enter_method(counters);
    simplify_statement(cx, counters, root, root)
}

fn simplify_statement(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    root: StatId,
    stat: StatId,
) -> io::Result<()> {
    for index in 0..cx.ir[stat].stats.len() {
        let child = cx.ir[stat].stats[index];
        simplify_statement(cx, counters, root, child)?;
    }
    if let Some(body) = cx.ir[stat].exprents {
        for index in 0..cx.ir[body].len() {
            let expr = cx.ir[body][index];
            if let Some(replacement) = simplify_expr(cx, counters, root, expr)? {
                cx.ir[body][index] = replacement;
            }
        }
    }
    Ok(())
}

fn simplify_expr(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    root: StatId,
    expr: ExprId,
) -> io::Result<Option<ExprId>> {
    let children: Vec<_> = Expr::children(&cx.ir, expr).collect();
    for child in children {
        if let Some(replacement) = simplify_expr(cx, counters, root, child)? {
            let offsets = cx.ir[child].bytecode.clone();
            Expr::replace(&mut cx.ir, expr, child, replacement);
            Expr::add_offsets(&mut cx.ir, replacement, offsets.as_ref());
        }
    }
    if matches!(cx.ir[expr].kind, ExprKind::Invocation(_)) {
        let result = contract(cx, counters, root, expr)?;
        return Ok((!Expr::equals(cx, expr, result)).then_some(result));
    }
    Ok(None)
}

/// `ConcatenationHelper.contractStringConcat` also serves other passes.
pub(crate) fn contract(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    root: StatId,
    expr: ExprId,
) -> io::Result<ExprId> {
    let ExprKind::Invocation(invoke) = &cx.ir[expr].kind else {
        return Ok(expr);
    };
    match invoke.name.as_str() {
        "toString" => {
            if let (Some(class @ (STRING_BUILDER | STRING_BUFFER)), Some(builder)) =
                (invoke.classname.as_deref(), invoke.instance)
            {
                let builder_type = VarType::with_value(CodeType::Object, 0, class);
                return contract_builder(cx, counters, expr, builder, &builder_type);
            }
        }
        "makeConcat" | "makeConcatWithConstants" => {
            return contract_dynamic(cx, counters, root, expr);
        }
        _ => {}
    }
    Ok(expr)
}

fn contract_builder(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    expr: ExprId,
    mut builder: ExprId,
    builder_type: &VarType,
) -> io::Result<ExprId> {
    let mut operands = Vec::new();
    loop {
        match &cx.ir[builder].kind {
            ExprKind::Invocation(append) if is_append(append, builder_type) => {
                operands.push(first_parameter(append)?);
                builder = append
                    .instance
                    .ok_or_else(|| invalid_data("Missing append receiver"))?;
            }
            ExprKind::New {
                new_type,
                constructor,
                ..
            } if new_type == builder_type => {
                let constructor = constructor
                    .ok_or_else(|| invalid_data("Missing string builder constructor"))?;
                let ExprKind::Invocation(init) = &cx.ir[constructor].kind else {
                    return Err(invalid_data("Invalid string builder constructor"));
                };
                match init.descriptor.params.as_slice() {
                    [] => {}
                    [ty] if *ty == VarType::VARTYPE_STRING => operands.push(first_parameter(init)?),
                    _ => return Ok(expr),
                }
                break;
            }
            _ => return Ok(expr),
        }
    }
    operands.reverse();
    let mut string_positions = 0;
    for (index, &operand) in operands.iter().take(2).enumerate() {
        if Expr::expr_type(cx, operand) == VarType::VARTYPE_STRING {
            string_positions |= index + 1;
        }
    }
    let offsets = cx.ir[expr].bytecode.clone();
    if string_positions == 0 {
        operands.insert(
            0,
            string_constant(&mut cx.ir, counters, "".into(), offsets.clone()),
        );
    }
    for (index, operand) in operands.iter_mut().enumerate() {
        let replacement = remove_value_of(&cx.ir, *operand)?;
        if index > 1
            || Expr::expr_type(cx, replacement) == VarType::VARTYPE_STRING
            || string_positions != index + 1
        {
            *operand = replacement;
        }
        if index == 0 {
            string_positions &= 2;
        }
    }
    Ok(create_concat(cx, counters, operands, offsets))
}

fn contract_dynamic(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    root: StatId,
    expr: ExprId,
) -> io::Result<ExprId> {
    let offsets = cx.ir[expr].bytecode.clone();
    let mut operands = extract_parameters(cx, counters, root, expr, &offsets)?;
    let starts_with_string = operands
        .iter()
        .take(2)
        .any(|&operand| Expr::expr_type(cx, operand) == VarType::VARTYPE_STRING);
    if !starts_with_string || operands.len() == 1 {
        let index = usize::from(operands.len() == 1);
        operands.insert(
            index,
            string_constant(&mut cx.ir, counters, "".into(), offsets.clone()),
        );
    }
    if operands.len() >= 2 {
        Ok(create_concat(cx, counters, operands, offsets))
    } else {
        Ok(expr)
    }
}

fn create_concat(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    operands: Vec<ExprId>,
    offsets: Option<BytecodeOffsets>,
) -> ExprId {
    let mut operands = operands.into_iter();
    let mut accumulated = operands.next().expect("Concatenation requires an operand");
    for operand in operands {
        let concat = Expr::function(
            &mut cx.ir,
            counters,
            FunctionType::StrConcat,
            vec![accumulated, operand],
            offsets.clone(),
        );
        let left = Expr::expr_type(cx, accumulated);
        let implicit = if left == VarType::VARTYPE_STRING {
            Expr::expr_type(cx, operand)
        } else {
            left
        };
        let ExprKind::Function { implicit_type, .. } = &mut cx.ir[concat].kind else {
            unreachable!()
        };
        *implicit_type = Some(Box::new(implicit));
        accumulated = concat;
    }
    accumulated
}

fn extract_parameters(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    root: StatId,
    expr: ExprId,
    offsets: &Option<BytecodeOffsets>,
) -> io::Result<Vec<ExprId>> {
    let ExprKind::Invocation(invoke) = &cx.ir[expr].kind else {
        unreachable!()
    };
    for index in 0..invoke.parameters.len() {
        let ExprKind::Invocation(invoke) = &cx.ir[expr].kind else {
            unreachable!()
        };
        let parameter = remove_value_of(&cx.ir, invoke.parameters[index])?;
        let ExprKind::Invocation(invoke) = &mut cx.ir[expr].kind else {
            unreachable!()
        };
        // Upstream replaces only the parameter list, including when an
        // invocation's receiver happens to alias its first parameter.
        invoke.parameters[index] = parameter;
    }

    let ExprKind::Invocation(invoke) = &cx.ir[expr].kind else {
        unreachable!()
    };
    let parameters = invoke.parameters.clone();
    let Some(recipe_arg) = invoke
        .bootstrap_arguments
        .as_deref()
        .and_then(|args| args.first())
    else {
        // makeConcat's empty bootstrap list has one argument tag per operand.
        return Ok(parameters);
    };
    let recipe_arg = recipe_arg
        .as_ref()
        .ok_or_else(|| invalid_data("Missing string concat recipe constant"))?;
    if recipe_arg.ty() != CONSTANT_STRING {
        return Ok(parameters);
    }
    let PooledConstant::Primitive(recipe) = recipe_arg else {
        return Err(invalid_data("Invalid string concat recipe constant"));
    };
    let recipe = match &recipe.value {
        ConstantValue::String(recipe) => recipe.clone(),
        ConstantValue::Null => return Ok(parameters),
        _ => return Err(invalid_data("Invalid string concat recipe text")),
    };

    let mut operands = Vec::new();
    let mut text = Vec::new();
    let mut args = parameters.into_iter();
    for unit in recipe.utf16() {
        if !matches!(unit, TAG_ARG | TAG_CONST) {
            text.push(unit);
            continue;
        }
        if !text.is_empty() {
            let value = JavaString::from_utf16(mem::take(&mut text));
            operands.push(string_constant(
                &mut cx.ir,
                counters,
                value,
                offsets.clone(),
            ));
        }
        // The upstream recipe reader currently omits bootstrap constants.
        if unit == TAG_ARG {
            if let Some(arg) = args.next() {
                operands.push(arg);
            } else {
                cx.ir[root]
                    .add_comment("$VF: Could not fully resugar string concatentation!", false);
            }
        }
    }
    if !text.is_empty() {
        operands.push(string_constant(
            &mut cx.ir,
            counters,
            JavaString::from_utf16(text),
            offsets.clone(),
        ));
    }
    Ok(operands)
}

fn string_constant(
    ir: &mut Ir,
    counters: &mut CounterContainer,
    value: JavaString,
    offsets: Option<BytecodeOffsets>,
) -> ExprId {
    Expr::new(
        ir,
        counters,
        Expr::constant(VarType::VARTYPE_STRING, ConstantValue::String(value), false),
        offsets,
    )
}

fn is_append(invoke: &Invocation, builder: &VarType) -> bool {
    invoke.name == "append"
        && invoke.descriptor.ret == *builder
        && matches!(invoke.descriptor.params.as_slice(), [param] if is_concat_primitive(param)
            || *param == VarType::VARTYPE_OBJECT || *param == VarType::VARTYPE_STRING)
}

fn remove_value_of(ir: &Ir, expr: ExprId) -> io::Result<ExprId> {
    if let ExprKind::Invocation(invoke) = &ir[expr].kind
        && invoke.name == "valueOf"
        && invoke.classname.as_deref() == Some(STRING)
        && let [param] = invoke.descriptor.params.as_slice()
        && (is_concat_primitive(param) || *param == VarType::VARTYPE_OBJECT)
    {
        return first_parameter(invoke);
    }
    Ok(expr)
}

fn is_concat_primitive(ty: &VarType) -> bool {
    matches!(
        ty.ty,
        CodeType::Boolean
            | CodeType::Char
            | CodeType::Double
            | CodeType::Float
            | CodeType::Int
            | CodeType::Long
    )
}

fn first_parameter(invoke: &Invocation) -> io::Result<ExprId> {
    invoke
        .parameters
        .first()
        .copied()
        .ok_or_else(|| invalid_data("Missing string concat parameter"))
}

fn invalid_data(message: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}
