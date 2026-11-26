// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! ClassWriter.classLambdaToJava and its anonymous-method body writer.

use super::{
    method_errors::dump_error, method_parameters::rename_parameter, with_method_for_writing,
};
use crate::code::code_constants::INIT_NAME;
use crate::decompiler::{
    expr_processor::get_cast_type_name,
    exps::{ExitType, Expr, ExprKind, FunctionType, generic_inference::Inference, literal, write},
    ir::{ExprId, StatId},
    stats::{StatementKind, write as statements},
    vars::var_version_pair::VarVersionPair,
};
use crate::engine::{
    Cx,
    class_nodes::{ClassNodeId, LambdaInformation},
    class_wrapper::{MethodSlot, catch_method_failure},
};
use crate::types::{MethodDescriptor, VarType};
use crate::util::text_buffer::TextBuffer;
use std::{io, sync::Arc};

pub(crate) fn write_lambda(
    cx: &mut Cx,
    node: ClassNodeId,
    buffer: &mut TextBuffer,
    receiver: Option<ExprId>,
    indent: i32,
) -> io::Result<()> {
    let Some(owner) = cx.class_nodes.wrapper_owner(node) else {
        return Ok(());
    };
    if cx.class_nodes[owner].wrapper.is_none() {
        return Ok(());
    }
    let info = cx.class_nodes[node]
        .lambda
        .clone()
        .ok_or_else(|| io::Error::other("Missing lambda metadata"))?;
    cx.with_class_node(node, |cx| {
        if info.is_method_reference {
            return write_reference(cx, buffer, &info, receiver, indent);
        }
        let slot = MethodSlot::by_key(cx, node, &info.content_method_key)
            .ok_or_else(|| io::Error::other("Missing lambda content method"))?;
        let content = MethodDescriptor::parse_descriptor(&info.content_method_descriptor);
        let signature = MethodDescriptor::parse_descriptor(&info.method_descriptor);
        let anonymous = cx.options.lambda_to_anonymous_class;
        if !anonymous {
            let root = slot.get(cx).root();
            if cx.options.mark_corresponding_synthetics {
                buffer
                    .append("/* ")
                    .append_method(
                        &info.content_method_name,
                        true,
                        &info.content_class_name,
                        &info.content_method_name,
                        &info.content_method_descriptor,
                    )
                    .append(" */ ");
            }
            if signature.params.as_slice() == [VarType::VARTYPE_INT] && signature.ret.array_dim > 0
            {
                let root =
                    root.ok_or_else(|| io::Error::other("Missing array constructor lambda body"))?;
                if is_array_constructor(cx, root, i32::from(!info.is_content_method_static)) {
                    buffer
                        .append_cast_type_name(cx, &signature.ret)
                        .append("::new");
                    return Ok(());
                }
            }
            let parens = signature.params.len() != 1;
            if parens {
                buffer.append_char('(');
            }
            write_parameters(cx, buffer, &info, slot, &content, &signature, false)?;
            if parens {
                buffer.append_char(')');
            }
            buffer.append(" ->");
            if cx.options.inline_simple_lambdas
                && slot.get(cx).decompile_error().is_none()
                && let Some(root) = root
                && write_simple(cx, node, slot, root, buffer, indent)?
            {
                return Ok(());
            }
        }
        buffer.append(" {").append_line_separator();
        with_method_for_writing(cx, node, slot.index, |cx| {
            let mut body_indent = indent + 1;
            if anonymous {
                buffer
                    .append_indent(body_indent)
                    .append("public ")
                    .append(&info.method_name)
                    .append_char('(');
                write_parameters(cx, buffer, &info, slot, &content, &signature, true)?;
                buffer.append(") {").append_line_separator();
                body_indent += 1;
            }
            if slot.get(cx).decompile_error().is_none()
                && let Some(root) = slot.get(cx).root()
            {
                let result = catch_method_failure(|| statements::to_java(cx, root, body_indent));
                match result {
                    Ok(mut code) => {
                        add_dummy_exit(cx, root, &mut code);
                        append_body(cx, slot, buffer, &code);
                    }
                    Err(error) => mark_error(cx, slot, error)?,
                }
            }
            if slot.get(cx).decompile_error().is_some() {
                let class = &cx.class_nodes[owner].class;
                dump_error(cx, buffer, class, slot.get(cx), body_indent);
            }
            if anonymous {
                buffer
                    .append_indent(body_indent - 1)
                    .append_char('}')
                    .append_line_separator();
            }
            Ok(())
        })?;
        buffer.append_indent(indent).append_char('}');
        Ok(())
    })
}

fn write_reference(
    cx: &mut Cx,
    buf: &mut TextBuffer,
    info: &LambdaInformation,
    receiver: Option<ExprId>,
    indent: i32,
) -> io::Result<()> {
    let owner = VarType::from_signature_cl(&info.content_class_name, true);
    if let Some(receiver) = receiver.filter(|_| !info.is_content_method_static) {
        Inference::for_writing(cx).infer(receiver, Some(&owner))?;
        let mut text = write::to_java(cx, receiver, indent)?;
        if matches!(
            cx.ir[receiver].kind,
            ExprKind::Function {
                op: FunctionType::Cast,
                needs_cast: true,
                ..
            }
        ) {
            text.enclose_with_parens();
        }
        buf.append_buffer(&text);
    } else {
        buf.append_cast_type_name(cx, &owner);
    }
    let name = if info.content_method_name == INIT_NAME {
        "new"
    } else {
        &info.content_method_name
    };
    buf.append("::").append_method(
        name,
        false,
        &info.content_class_name,
        &info.content_method_name,
        &info.content_method_descriptor,
    );
    Ok(())
}

fn is_array_constructor(cx: &Cx, root: StatId, index: i32) -> bool {
    let Some(first) = cx.ir[root].first else {
        return false;
    };
    if !matches!(cx.ir[first].kind, StatementKind::BasicBlock { .. }) {
        return false;
    }
    let Some(list) = cx.ir[first].exprents else {
        return false;
    };
    let [exit] = cx.ir[list].as_slice() else {
        return false;
    };
    let ExprKind::Exit {
        value: Some(value), ..
    } = cx.ir[*exit].kind
    else {
        return false;
    };
    let ExprKind::New {
        new_type,
        direct_array_init,
        array_elements,
        dimensions,
        ..
    } = &cx.ir[value].kind
    else {
        return false;
    };
    new_type.array_dim > 0
        && !direct_array_init
        && array_elements.is_empty()
        && dimensions
            .last()
            .and_then(|&id| Expr::variable(&cx.ir, id))
            .is_some_and(|v| v.index == index)
}

fn write_parameters(
    cx: &mut Cx,
    buf: &mut TextBuffer,
    info: &LambdaInformation,
    slot: MethodSlot,
    content: &MethodDescriptor,
    sam: &MethodDescriptor,
    as_method: bool,
) -> io::Result<()> {
    let method = Arc::clone(&slot.get(cx).method);
    let captured = content.params.len().saturating_sub(sam.params.len());
    for (i, (index, ty)) in content
        .parameter_slots(info.is_content_method_static)
        .skip(captured)
        .enumerate()
    {
        if i != 0 {
            buf.append(", ");
        }
        if as_method {
            let name = get_cast_type_name(cx, ty);
            let name = if name == "<undefinedtype>" && cx.options.undefined_as_object {
                get_cast_type_name(cx, &VarType::VARTYPE_OBJECT)
            } else {
                name
            };
            buf.append_cast_type_name_with(cx, &name, ty)
                .append_char(' ');
        }
        let vars = &cx.ir[slot.get(cx).variables];
        let pair = VarVersionPair::new(index, 0);
        let name = if as_method {
            None
        } else {
            vars.clashing_names.get(&pair)
        }
        .or_else(|| vars.names.get(&pair).and_then(Option::as_ref))
        .map_or_else(|| format!("param{index}"), ToString::to_string);
        let name = rename_parameter(cx, &method, ty, Some(name.into()), index)?
            .ok_or_else(|| io::Error::other("Missing renamed lambda parameter"))?;
        let (class, method_name) = if as_method {
            (
                &cx.class_nodes[slot.node].class.qualified_name,
                &info.method_name,
            )
        } else {
            (&info.content_class_name, &info.content_method_name)
        };
        buf.append_variable(
            &name,
            true,
            true,
            class,
            method_name,
            content.clone(),
            index,
            &name,
        );
    }
    Ok(())
}

fn write_simple(
    cx: &mut Cx,
    node: ClassNodeId,
    slot: MethodSlot,
    root: StatId,
    buf: &mut TextBuffer,
    indent: i32,
) -> io::Result<bool> {
    let Some(first) = cx.ir[root].first else {
        return Ok(false);
    };
    if !matches!(cx.ir[first].kind, StatementKind::BasicBlock { .. }) {
        return Ok(false);
    }
    let Some(list) = cx.ir[first].exprents else {
        return Ok(false);
    };
    let expr = match cx.ir[list].as_slice() {
        [] => {
            buf.append(" {}");
            return Ok(true);
        }
        [expr] => *expr,
        _ => return Ok(false),
    };
    if matches!(
        cx.ir[expr].kind,
        ExprKind::Exit {
            kind: ExitType::Throw,
            ..
        }
    ) || matches!(cx.ir[expr].kind,ExprKind::Assignment {left,..} if Expr::variable(&cx.ir,left).is_some_and(|v|v.definition))
    {
        return Ok(false);
    }
    with_method_for_writing(cx, node, slot.index, |cx| {
        let result = catch_method_failure(|| {
            let mut code = write::to_java(cx, expr, indent)?;
            if matches!(cx.ir[expr].kind, ExprKind::Exit { .. }) {
                code.set_start(6);
            } else {
                code.prepend(" ");
            }
            add_dummy_exit(cx, root, &mut code);
            append_body(cx, slot, buf, &code);
            Ok(())
        });
        if let Err(error) = result {
            mark_error(cx, slot, error)?;
            buf.append(" // $VF: Couldn't be decompiled");
        }
        Ok(true)
    })
}

fn add_dummy_exit(cx: &Cx, root: StatId, buf: &mut TextBuffer) {
    if let StatementKind::Root { dummy_exit, .. } = cx.ir[root].kind
        && let StatementKind::DummyExit { bytecode } = &cx.ir[dummy_exit].kind
    {
        literal::add_offsets(buf, bytecode.as_ref());
    }
}

fn append_body(cx: &Cx, slot: MethodSlot, buf: &mut TextBuffer, body: &TextBuffer) {
    let method = &slot.get(cx).method;
    let key = crate::util::interpreter_util::make_unique_key(&method.name, &method.descriptor);
    buf.append_buffer_for(
        body,
        Some(&cx.class_nodes[slot.node].class.qualified_name),
        Some(&key),
    );
}

fn mark_error(cx: &mut Cx, slot: MethodSlot, error: io::Error) -> io::Result<()> {
    if error.kind() == io::ErrorKind::Interrupted {
        return Err(error);
    }
    log::warn!(
        "Method {} couldn't be written: {error}",
        slot.get(cx).method
    );
    slot.get_mut(cx).write_error = Some(error);
    Ok(())
}
