// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Write assignments with the type inferred for their destination.

use std::io;

use super::{
    casts::{CastOptions, NullCastType, append_casted},
    to_java as expression,
};
use crate::code::code_constants::ACC_FINAL;
use crate::decompiler::expr_processor::get_cast_type_name;
use crate::decompiler::exps::{
    Expr, ExprKind, FunctionType, generic_inference::Inference, literal,
};
use crate::decompiler::ir::ExprId;
use crate::engine::Cx;
use crate::structs::StructMember;
use crate::util::{interpreter_util::make_unique_key, text_buffer::TextBuffer};

pub(super) fn to_java(cx: &mut Cx, expr: ExprId, indent: i32) -> io::Result<TextBuffer> {
    let ExprKind::Assignment {
        left,
        right,
        compound,
    } = cx.ir[expr].kind
    else {
        unreachable!()
    };
    let left_type = Inference::for_writing(cx).infer(left, None)?;
    let field = assignment_field(cx, left);
    let mut buffer = TextBuffer::new(cx);
    if field == AssignmentField::Hidden {
        return Ok(buffer);
    }
    if field == AssignmentField::FinalStatic {
        let ExprKind::Field(field) = &cx.ir[left].kind else {
            unreachable!()
        };
        let owner = field
            .classname
            .as_deref()
            .ok_or_else(|| invalid("Field has no declaring class"))?;
        buffer.append_field_with(
            &field.name,
            false,
            owner,
            &field.name,
            field.descriptor.clone(),
        );
    } else {
        buffer.append_buffer(&expression(cx, left, indent)?);
    }

    literal::adjust_const_type(&mut cx.ir, right, &left_type);
    optimize_cast(cx, left, right)?;
    if let Some(op) = compound {
        buffer
            .append_char(' ')
            .append(op.java_operator())
            .append("= ");
        buffer.append_buffer(&expression(cx, right, indent)?);
    } else {
        buffer.append(" = ");
        let cast_name = cx.with_locked_imports(|cx| get_cast_type_name(cx, &left_type));
        if cast_name == "<unrepresentable>" {
            buffer.append_buffer(&expression(cx, right, indent)?);
        } else {
            append_casted(
                cx,
                right,
                &left_type,
                &mut buffer,
                indent,
                CastOptions {
                    null_cast: NullCastType::DontCastAtAll,
                    cast_always: false,
                    cast_narrowing: false,
                    unbox: false,
                },
            )?;
        }
    }

    if let Some(offsets) = &cx.ir[expr].bytecode {
        for offset in offsets.iter() {
            buffer.add_start_bytecode_mapping(offset as i32);
        }
    }
    if cx.options.decompiler_comments
        && let Some(variable) = Expr::variable(&cx.ir, left)
        && variable.definition
        && let Some(owner) = variable.processor
        && cx.ir[owner].synthetic_semaphores.contains(&variable.index)
    {
        buffer.append(" /* VF: Semaphore variable */");
    }
    Ok(buffer)
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum AssignmentField {
    Regular,
    FinalStatic,
    Hidden,
}

fn assignment_field(cx: &Cx, left: ExprId) -> AssignmentField {
    let ExprKind::Field(field) = &cx.ir[left].kind else {
        return AssignmentField::Regular;
    };
    let Some(node) = cx
        .current_class_node
        .as_deref()
        .and_then(|name| cx.class_nodes.id(name))
    else {
        return AssignmentField::Regular;
    };
    let Some(declaration) = cx.class_nodes[node]
        .class
        .get_field(&field.name, &field.descriptor.descriptor_string)
    else {
        return AssignmentField::Regular;
    };
    if let Some(owner) = cx.class_nodes.wrapper_owner(node)
        && cx.class_nodes[owner].wrapper.is_some()
        && cx.class_nodes[owner]
            .hidden_members
            .contains(&make_unique_key(&declaration.name, &declaration.descriptor))
    {
        AssignmentField::Hidden
    } else if field.is_static() && declaration.has_modifier(ACC_FINAL) {
        AssignmentField::FinalStatic
    } else {
        AssignmentField::Regular
    }
}

fn optimize_cast(cx: &mut Cx, left: ExprId, right: ExprId) -> io::Result<()> {
    let ExprKind::Function {
        op: FunctionType::Cast,
        operands,
        needs_cast,
        ..
    } = &cx.ir[right].kind
    else {
        return Ok(());
    };
    let value = operands[0];
    let target = operands[1];
    if !needs_cast
        && Expr::variable(&cx.ir, left).is_some()
        && let (Some(from), Some(to)) = (
            Expr::expr_type(cx, right).value,
            Expr::expr_type(cx, target).value,
        )
        && cx.classes().instance_of(&from, &to)
        && Expr::expr_type(cx, left).array_dim > Expr::expr_type(cx, value).array_dim
    {
        let ExprKind::Function { needs_cast, .. } = &mut cx.ir[right].kind else {
            unreachable!()
        };
        *needs_cast = true;
        return Ok(());
    }

    let ty = Inference::for_writing(cx).infer(left, None)?;
    if !ty.is_generic_type() {
        return Ok(());
    }
    let Some(method) = cx.writing_method() else {
        return Ok(());
    };
    let Some(signature) = method.method.shared_signature().cloned() else {
        return Ok(());
    };
    let formal = signature.get();
    let Some(index) = formal
        .type_parameters
        .iter()
        .position(|name| Some(name.as_str()) == ty.value.as_deref())
    else {
        return Ok(());
    };
    let class = cx
        .class_nodes
        .get(&method.method.class_qualified_name)
        .ok_or_else(|| invalid("Missing assignment method's declaring class"))?;
    let bounds = if let Some(class) = class.class.signature() {
        signature.update(|method| {
            let types = &mut method.type_parameter_bounds[index];
            for ty in types.clone() {
                if let Some(class_index) = class
                    .fparameters
                    .iter()
                    .position(|name| Some(name.as_str()) == ty.value.as_deref())
                {
                    types.extend(class.fbounds[class_index].iter().cloned());
                }
            }
            types.clone()
        })
    } else {
        formal.type_parameter_bounds[index].clone()
    };

    let target_type = Inference::for_writing(cx).infer(target, Some(&ty))?;
    if !bounds.is_empty() {
        let value = target_type
            .value
            .ok_or_else(|| invalid("Malformed generic cast target"))?;
        if bounds
            .iter()
            .any(|bound| bound.value.as_ref() == Some(&value))
        {
            let ExprKind::Constant { var_type, .. } = &mut cx.ir[target].kind else {
                return Err(invalid("Generic cast target is not a type constant"));
            };
            *var_type = ty;
            Inference::for_writing(cx).infer(right, None)?;
        }
    }
    Ok(())
}

fn invalid(message: &str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}
