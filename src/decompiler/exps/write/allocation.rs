// Copyright 2000-2024 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! NewExprent writes array, qualified, anonymous, enum and lambda allocations.

use super::{
    casts::{CastOptions, append_casted},
    invalid, invocation, lambda_types,
};
use crate::code::code_constants::ACC_STATIC;
use crate::decompiler::{
    expr_processor::{get_cast_type_name, type_name},
    exps::{Expr, ExprKind, Invocation, WriteFlags, literal},
    ir::ExprId,
    vars::var_version_pair::VarVersionPair,
};
use crate::engine::{Cx, class_nodes::ClassKind, class_writer};
use crate::types::{CodeType, VarType};
use crate::util::text_buffer::TextBuffer;
use std::io;

pub(super) fn to_java(cx: &mut Cx, expr: ExprId, indent: i32) -> io::Result<TextBuffer> {
    let ExprKind::New {
        new_type,
        dimensions,
        constructor,
        array_elements,
        anonymous,
        lambda,
        direct_array_init,
        ..
    } = &cx.ir[expr].kind
    else {
        unreachable!()
    };
    let ty = new_type.clone();
    let constructor = *constructor;
    let flags = cx.ir[expr].write_flags;
    let enum_const = flags.contains(WriteFlags::ENUM_CONST);
    let mut buf = TextBuffer::new(cx);
    if *anonymous {
        return anonymous_instance(cx, expr, &ty, constructor, *lambda, enum_const, indent);
    }
    if *direct_array_init {
        let elements = array_elements.clone();
        buf.append_char('{');
        if !elements.is_empty() {
            buf.push_newline_group(indent, 2)
                .append_possible_newline()
                .push_newline_group(indent, 0);
            append_elements(
                cx,
                &mut buf,
                &elements,
                &ty.decrease_array_dim(),
                indent,
                false,
            )?;
            buf.pop_newline_group()
                .append_possible_newline_or("", true)
                .pop_newline_group();
        }
        buf.append_char('}');
    } else if ty.array_dim == 0 {
        if !enum_const {
            let qualified = write_enclosing(cx, &mut buf, ty.name(), constructor, indent)?;
            let name = type_name(cx, &ty, true);
            let name = allocation_name(cx, &ty, name, qualified)?;
            buf.append("new ").append_type_name_with(cx, &name, &ty);
        }
        if let Some(id) = constructor
            && (!enum_const || call(cx, id)?.parameters.len() > 2)
        {
            append_constructor(cx, &mut buf, id, indent)?;
        }
    } else if flags.contains(WriteFlags::VARARG) {
        let elements = array_elements.clone();
        append_elements(
            cx,
            &mut buf,
            &elements,
            &ty.decrease_array_dim(),
            indent,
            true,
        )?;
        if let [only] = elements.as_ref() {
            let element_ty = Expr::expr_type(cx, *only);
            if element_ty.ty == CodeType::Object
                && element_ty.name() == "java/lang/Object"
                && element_ty.array_dim > 0
            {
                buf.prepend("(Object)")
                    .add_class_token(1, 6, "java/lang/Object");
            }
        }
    } else if array_elements.is_empty() {
        let dimensions = dimensions.clone();
        buf.append("new ").append_type_name(cx, &ty);
        for i in 0..ty.array_dim as usize {
            buf.append_char('[');
            if let Some(&dim) = dimensions.get(i) {
                literal::adjust_const_type(&mut cx.ir, dim, &VarType::VARTYPE_INT);
                buf.append_buffer(&super::to_java(cx, dim, indent)?);
            }
            buf.append_char(']');
        }
    } else {
        let elements = array_elements.clone();
        buf.append("new ").append_type_name(cx, &ty);
        for _ in 0..ty.array_dim {
            buf.append("[]");
        }
        buf.append_char('{')
            .push_newline_group(indent, 1)
            .append_possible_newline()
            .push_newline_group(indent, 0);
        append_elements(
            cx,
            &mut buf,
            &elements,
            &ty.decrease_array_dim(),
            indent,
            false,
        )?;
        buf.pop_newline_group()
            .append_possible_newline_or("", true)
            .append_char('}')
            .pop_newline_group();
    }
    Ok(buf)
}

fn append_elements(
    cx: &mut Cx,
    buf: &mut TextBuffer,
    elements: &[ExprId],
    ty: &VarType,
    indent: i32,
    vararg: bool,
) -> io::Result<()> {
    for (i, &element) in elements.iter().enumerate() {
        if i > 0 {
            buf.append_char(',').append_possible_newline_or(" ", false);
        }
        // An explicitly allocated nested array must retain its type when its
        // parent is expanded into a varargs argument list.
        if vararg
            && let ExprKind::New {
                direct_array_init, ..
            } = &mut cx.ir[element].kind
        {
            *direct_array_init = false;
        }
        append_casted(cx, element, ty, buf, indent, CastOptions::default())?;
    }
    Ok(())
}

fn anonymous_instance(
    cx: &mut Cx,
    expr: ExprId,
    ty: &VarType,
    constructor: Option<ExprId>,
    lambda: bool,
    enum_const: bool,
    indent: i32,
) -> io::Result<TextBuffer> {
    let child = cx
        .class_nodes
        .id(ty.name())
        .ok_or_else(|| invalid("Missing anonymous class node"))?;
    let self_reference = cx.current_node() == Some(child);
    let as_class = cx.options.lambda_to_anonymous_class;
    let mut buf = TextBuffer::new(cx);
    if !enum_const && (!lambda || as_class) {
        let base = cx.class_nodes[child]
            .anonymous_type
            .clone()
            .ok_or_else(|| invalid("Missing anonymous class supertype"))?;
        let qualified = !lambda && write_enclosing(cx, &mut buf, base.name(), constructor, indent)?;
        buf.append("new ");
        if self_reference {
            buf.append("<anonymous constructor>");
        } else {
            let name = get_cast_type_name(cx, &base);
            let name = allocation_name(cx, &base, name, qualified)?;
            let signature = cx.class_nodes.wrapper_owner(child).and_then(|owner| {
                let owner = &cx.class_nodes[owner];
                owner.wrapper.as_ref()?;
                owner.class.signature()
            });
            if let Some(sig) = signature {
                if sig.superinterfaces.len() > 1 && !lambda {
                    log::warn!(
                        "Inconsistent anonymous class signature: {}",
                        cx.class_nodes[child].class.qualified_name
                    );
                }
                buf.append_cast_type_name(
                    cx,
                    sig.superinterfaces.first().unwrap_or(&sig.superclass),
                );
            } else {
                buf.append_cast_type_name_with(cx, &name, &base);
            }
        }
    }
    if let Some(constructor) = constructor.filter(|_| !lambda) {
        append_constructor(cx, &mut buf, constructor, indent)?;
    } else {
        if let ExprKind::New {
            generics: Some(state),
            ..
        } = &cx.ir[expr].kind
        {
            let args = state.arguments.clone();
            invocation::append_type_arguments(cx, &mut buf, &args);
        }
        buf.append("()");
    }
    if enum_const && buf.length() == 2 {
        buf.set_length(0);
    }
    if lambda {
        if !as_class {
            buf.set_length(0);
        }
        lambda_types::set(cx, expr, child, constructor)?;
        let receiver = constructor
            .map(|id| call(cx, id).map(|inv| inv.instance))
            .transpose()?
            .flatten();
        class_writer::write_lambda(cx, child, &mut buf, receiver, indent)?;
    } else if !self_reference {
        class_writer::write_class(cx, child, &mut buf, indent)?;
    }
    Ok(buf)
}

fn call(cx: &Cx, id: ExprId) -> io::Result<&Invocation> {
    match &cx.ir[id].kind {
        ExprKind::Invocation(call) => Ok(call),
        _ => Err(invalid("New expression constructor is not an invocation")),
    }
}

fn append_constructor(
    cx: &mut Cx,
    buf: &mut TextBuffer,
    id: ExprId,
    indent: i32,
) -> io::Result<()> {
    invocation::append_invocation_type_arguments(cx, id, buf);
    buf.append_char('(')
        .append_buffer(&invocation::append_param_list(cx, id, indent)?)
        .append_char(')');
    Ok(())
}

fn write_enclosing(
    cx: &mut Cx,
    buf: &mut TextBuffer,
    owner: &str,
    constructor: Option<ExprId>,
    indent: i32,
) -> io::Result<bool> {
    let Some(constructor) = constructor else {
        return Ok(false);
    };
    let first = call(cx, constructor)?.parameters.first().copied();
    if let Some(enclosing) = qualified_instance(cx, owner, first, indent)? {
        buf.append_buffer(&enclosing).append_char('.');
        Ok(true)
    } else {
        Ok(false)
    }
}

pub(super) fn qualified_instance(
    cx: &mut Cx,
    owner: &str,
    first: Option<ExprId>,
    indent: i32,
) -> io::Result<Option<TextBuffer>> {
    let Some(node) = cx.class_nodes.get(owner) else {
        return Ok(None);
    };
    if matches!(node.kind, ClassKind::Root | ClassKind::Local) || node.access & ACC_STATIC != 0 {
        return Ok(None);
    }
    let Some(first) = first else { return Ok(None) };
    if let ExprKind::Variable(var) = &cx.ir[first].kind {
        let class = cx
            .current_node()
            .ok_or_else(|| invalid("Missing current class for qualified allocation"))?;
        let vars = var
            .processor
            .ok_or_else(|| invalid("Missing enclosing variable processor"))?;
        let this = cx.ir[vars]
            .this_vars
            .get(&VarVersionPair::new(var.index, var.version));
        if this == Some(&cx.class_nodes[class].class.qualified_name) {
            return Ok(None);
        }
    }
    super::to_java(cx, first, indent).map(Some)
}

fn allocation_name(cx: &Cx, ty: &VarType, name: String, qualified: bool) -> io::Result<String> {
    if !qualified {
        return Ok(name);
    }
    if let Some(node) = cx.class_nodes.get(ty.name()) {
        return node
            .simple_name
            .as_ref()
            .map(ToString::to_string)
            .ok_or_else(|| invalid("Missing qualified allocation name"));
    }
    Ok(name.rsplit('.').next().unwrap().to_owned())
}
