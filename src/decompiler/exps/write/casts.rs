//! Expected-type conversions applied while writing an expression.

use std::io;

use crate::decompiler::expr_processor::type_name;
use crate::decompiler::exps::generic_inference::Inference;
use crate::decompiler::exps::literal::adjust_const_type;
use crate::decompiler::exps::{Expr, ExprKind, FunctionType, WriteFlags};
use crate::decompiler::ir::ExprId;
use crate::engine::Cx;
use crate::structs::consts::PooledConstant;
use crate::types::{CodeType, GenericType, NamedGenerics, VarType};
use crate::util::text_buffer::TextBuffer;

use super::{functions::precedence, to_java};

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) enum NullCastType {
    Cast,
    #[default]
    DontCast,
    DontCastAtAll,
}

#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct CastOptions {
    pub null_cast: NullCastType,
    pub cast_always: bool,
    pub cast_narrowing: bool,
    pub unbox: bool,
}

/// `ExprProcessor.getCastedExprent`. The result reports a regular cast, which
/// also disables the varargs spelling of an array creation.
pub(crate) fn append_casted(
    cx: &mut Cx,
    mut expr: ExprId,
    left_type: &VarType,
    buf: &mut TextBuffer,
    indent: i32,
    options: CastOptions,
) -> io::Result<bool> {
    let mut left = left_type.clone();
    if options.unbox
        && let ExprKind::Invocation(call) = &cx.ir[expr].kind
        && call.is_boxing_call(cx)
        && !call.force_boxing
    {
        expr = call.parameters[0];
        let parameter = call.descriptor.params[0].ty;
        if let ExprKind::Constant { var_type, .. } = &cx.ir[expr].kind
            && var_type.ty != parameter
        {
            left = VarType::new(parameter);
        }
    }

    let mut inference = Inference::for_writing(cx);
    let right = inference.infer(expr, Some(&left))?;
    narrow_generic_cast(inference.cx, expr, &left);
    let do_cast = !left.higher_equal_in_lattice_than(inference.cx, &right)
        && (right == VarType::VARTYPE_OBJECT || left.ty != CodeType::Object);
    let cast_null = options.null_cast == NullCastType::Cast
        && right.ty == CodeType::Null
        && type_name(inference.cx, &left, true) != "<undefinedtype>";
    let narrow = options.cast_narrowing
        && is_int_constant(inference.cx, expr)
        && (VarType::VARTYPE_INT.higher_in_lattice_than(inference.cx, &left)
            || left == VarType::VARTYPE_BYTE_OBJ
            || left == VarType::VARTYPE_SHORT_OBJ);
    let cast_generics =
        generic_types_cast(&inference.named_generics(), inference.cx, &left, &right);
    let cx = inference.cx;
    let cast = options.cast_always
        || ((options.null_cast != NullCastType::DontCastAtAll || right.ty != CodeType::Null)
            && (do_cast || cast_null || narrow || cast_generics));

    let cast_lambda = !cast && left != right && lambda_needs_cast(cx, &left, expr)?;
    let quote = cast && precedence(cx, expr)? >= FunctionType::Cast.java_precedence();
    if options.cast_narrowing
        && matches!(&cx.ir[expr].kind, ExprKind::Constant { var_type, .. } if var_type.ty != CodeType::Null)
    {
        if left == VarType::VARTYPE_BYTE_OBJ {
            left = VarType::VARTYPE_BYTE;
        } else if left == VarType::VARTYPE_SHORT_OBJ {
            left = VarType::VARTYPE_SHORT;
        }
    }
    if cast {
        buf.append("(").append_cast_type_name(cx, &left).append(")");
    }
    if cast_lambda {
        buf.append("(")
            .append_cast_type_name(cx, &right)
            .append(")");
    }
    if quote {
        buf.append("(");
    }

    adjust_const_type(&mut cx.ir, expr, &left);
    if cast && matches!(cx.ir[expr].kind, ExprKind::New { .. }) {
        cx.ir[expr].write_flags.remove(WriteFlags::VARARG);
    }
    buf.append_buffer(&to_java(cx, expr, indent)?);
    if quote {
        buf.append(")");
    }
    Ok(cast)
}

fn is_int_constant(cx: &Cx, expr: ExprId) -> bool {
    matches!(&cx.ir[expr].kind, ExprKind::Constant { var_type, .. }
        if matches!(var_type.ty, CodeType::Byte | CodeType::Bytechar | CodeType::Short | CodeType::Shortchar | CodeType::Int))
}

fn narrow_generic_cast(cx: &mut Cx, expr: ExprId, upper: &VarType) {
    if !upper.is_generic() || upper.arguments().is_empty() {
        return;
    }
    let ExprKind::Function {
        op: FunctionType::Cast,
        operands,
        needs_cast,
        ..
    } = &cx.ir[expr].kind
    else {
        return;
    };
    let target = operands[1];
    let kept = *needs_cast;
    let ty = Expr::expr_type(cx, target);
    if ty.value != upper.value {
        return;
    }
    if !ty.is_generic() {
        let ExprKind::Constant { var_type, .. } = &mut cx.ir[target].kind else {
            unreachable!("Cast target is not a type constant")
        };
        *var_type = upper.clone();
    } else if !kept && upper.equals_exact(&ty) {
        let ExprKind::Function { needs_cast, .. } = &mut cx.ir[expr].kind else {
            unreachable!()
        };
        *needs_cast = true;
    }
}

fn generic_types_cast(named: &NamedGenerics, cx: &Cx, left: &VarType, right: &VarType) -> bool {
    left.is_generic()
        && right.is_generic()
        && (should_cast_generic(named, cx, left, right)
            || (left.arguments().len() == right.arguments().len()
                && left
                    .arguments()
                    .iter()
                    .zip(right.arguments())
                    .any(|(left, right)| {
                        left.as_ref().is_some_and(|left| {
                            right
                                .as_ref()
                                .is_none_or(|right| should_cast_generic(named, cx, left, right))
                        })
                    })))
}

fn should_cast_generic(named: &NamedGenerics, cx: &Cx, left: &VarType, right: &VarType) -> bool {
    let no = GenericType::WILDCARD_NO;
    let extends = GenericType::WILDCARD_EXTENDS;
    let super_ = GenericType::WILDCARD_SUPER;
    if !left.is_generic() {
        return false;
    }
    let left_wildcard = left.wildcard();
    if !right.is_generic() {
        return left_wildcard == no && left.arguments().is_empty();
    }
    let right_wildcard = right.wildcard();
    if left.higher_equal_in_lattice_than(cx, right) {
        if right_wildcard == super_
            && (left_wildcard == no
                || (left_wildcard == extends
                    && (left.arguments().is_empty()
                        || right.arguments().is_empty()
                        || left != right)))
        {
            return true;
        }
    } else if (left_wildcard == extends && right_wildcard == super_)
        || (left.ty == CodeType::Genvar
            && right.ty == CodeType::Genvar
            && left_wildcard == no
            && [left, right].into_iter().all(|ty| {
                named
                    .get(ty)
                    .is_some_and(|bounds| bounds.contains(&VarType::VARTYPE_OBJECT))
            }))
    {
        return true;
    }
    if (left_wildcard == no || left_wildcard == super_) && right_wildcard == extends {
        return true;
    }
    left_wildcard == right_wildcard
        && left.arguments().len() == right.arguments().len()
        && left
            .arguments()
            .iter()
            .zip(right.arguments())
            .any(|(left, right)| match (left, right) {
                (Some(left), None) => left.ty == CodeType::Genvar,
                (Some(left), Some(right)) => should_cast_generic(named, cx, left, right),
                _ => false,
            })
}

fn lambda_needs_cast(cx: &Cx, left: &VarType, expr: ExprId) -> io::Result<bool> {
    let ExprKind::New {
        new_type,
        constructor,
        lambda: true,
        method_reference: false,
        ..
    } = &cx.ir[expr].kind
    else {
        return Ok(false);
    };
    let Some(class) = left
        .value
        .as_deref()
        .and_then(|name| cx.classes().get_class(name))
    else {
        return Ok(true);
    };
    let Some(node) = new_type
        .value
        .as_deref()
        .and_then(|name| cx.class_nodes.get(name))
    else {
        return Ok(class.get_method_by_key("").is_none());
    };
    let Some(ctor) = constructor else {
        return Ok(class.get_method_by_key("").is_none());
    };
    let ExprKind::Invocation(call) = &cx.ir[*ctor].kind else {
        unreachable!("Lambda allocation constructor is not an invocation")
    };
    let sam = match call
        .bootstrap_arguments
        .as_deref()
        .and_then(|args| args.first())
    {
        Some(Some(PooledConstant::Primitive(desc))) => desc.get_string(),
        _ => {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "Missing LambdaMetafactory SAM descriptor",
            ));
        }
    };
    let metadata = node.lambda.as_ref().expect("Missing lambda metadata");
    Ok(class
        .get_method(&metadata.method_name, sam.as_str())
        .is_none())
}
