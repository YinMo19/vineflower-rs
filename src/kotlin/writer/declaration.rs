// SPDX-License-Identifier: Apache-2.0

use std::{io, sync::Arc};

use super::{annotations, modifiers, write_class};
use crate::{
    code::code_constants::*,
    decompiler::expr_processor::get_cast_type_name,
    engine::{
        Cx,
        class_nodes::{ClassKind, ClassNodeId},
        class_writer::{
            comments::{self, RenameKind},
            declaration as java, javadoc,
        },
    },
    kotlin::{
        declarations::KType,
        identifier,
        member_writer::{DefaultArgsMap, visibility},
        members::{self, ClassElement},
        metadata::{
            flags,
            proto::{Modality, class::Kind},
        },
        types::kotlin_type,
    },
    structs::attr::TypeAnnotationData,
    types::VarType,
    util::text_buffer::TextBuffer,
};

pub(super) fn definition(
    cx: &mut Cx,
    node: ClassNodeId,
    buffer: &mut TextBuffer,
    indent: i32,
    data: Option<&ClassElement>,
    kflags: i32,
) -> io::Result<()> {
    let current = &cx.class_nodes[node];
    if current.kind == ClassKind::Anonymous {
        let Some(ClassElement::Class(data)) = data else {
            return Err(io::Error::other(
                "Anonymous class does not have Class Kotlin metadata",
            ));
        };
        buffer.append("object");
        let mut separator = " : ";
        for proto in &data.proto.supertype {
            let names = data
                .names
                .as_ref()
                .ok_or_else(|| io::Error::other("Missing Kotlin supertype name resolver"))?;
            let ty = KType::from_proto(Some(proto), names)?;
            if ty.jvm != VarType::VARTYPE_OBJECT {
                let mut text = TextBuffer::new(cx);
                ty.write(cx, &mut text, indent)?;
                buffer.append(separator).append_buffer(&text);
                separator = ", ";
            }
        }
        return Ok(());
    }
    let class = current.class.clone();
    let name = current
        .simple_name
        .clone()
        .ok_or_else(|| io::Error::other("Missing class name"))?;
    let access = if current.kind == ClassKind::Root {
        class.access_flags
    } else {
        current.access
    };
    let is_enum = cx.options.decompile_enums && access & ACC_ENUM != 0;
    let is_interface = access & ACC_INTERFACE != 0;
    let is_annotation = access & ACC_ANNOTATION != 0;
    java::append_deprecation(buffer, &class.attributes, indent);
    let old = cx
        .pool_interceptor
        .as_ref()
        .and_then(|pool| pool.get_old_name(&class.qualified_name))
        .map(str::to_owned);
    comments::append_rename_comment(cx, buffer, old.as_deref(), RenameKind::Class, indent)?;
    if let Some(doc) = cx.javadoc.as_ref().and_then(|p| p.class_doc(&class)) {
        javadoc::append(buffer, javadoc::JavadocStyle::Html, &doc, indent);
    }
    annotations::append(cx, buffer, indent, class.as_ref(), -1)?;
    annotations::append_jvm(
        buffer,
        indent,
        class.as_ref(),
        is_interface,
        false,
        &class.pool,
        TypeAnnotationData::CLASS_TYPE_PARAMETER,
    )?;
    buffer.append_indent(indent);
    visibility(
        cx,
        buffer,
        flags::VISIBILITY
            .get(kflags)
            .ok_or_else(|| io::Error::other("Invalid Kotlin class visibility"))?,
    );
    if flags::IS_EXPECT_CLASS.get(kflags) {
        buffer.append("expect ");
    }
    buffer.append(match flags::MODALITY.get(kflags) {
        Some(Modality::Final) if is_interface => "final ",
        Some(Modality::Open) if !is_interface => "open ",
        Some(Modality::Abstract) if !is_interface => "abstract ",
        Some(Modality::Sealed) => "sealed ",
        _ => "",
    });
    for (flag, word) in [
        (flags::IS_EXTERNAL_CLASS, "external "),
        (flags::IS_INNER, "inner "),
        (flags::IS_FUN_INTERFACE, "fun "),
        (flags::IS_VALUE_CLASS, "value "),
        (flags::IS_DATA, "data "),
    ] {
        if flag.get(kflags) {
            buffer.append(word);
        }
    }
    let kind = flags::CLASS_KIND.get(kflags);
    buffer.append(if is_enum {
        "enum class"
    } else if is_interface {
        "interface"
    } else if is_annotation {
        "annotation class"
    } else {
        match kind {
            Some(Kind::Object) => "object",
            Some(Kind::CompanionObject) => "companion object",
            _ => "class",
        }
    });
    if kind != Some(Kind::CompanionObject) || name != "Companion" {
        buffer.append_char(' ').append(&identifier(&name));
    }
    let supertype = class
        .super_class
        .as_ref()
        .map(|c| VarType::from_signature_cl(c.get_string(), true));
    let interfaces: Vec<_> = class
        .interface_names
        .iter()
        .map(|n| VarType::from_signature_cl(n, true))
        .collect();
    let signature = java::verify_class_signature(cx, &class, supertype.as_ref(), &interfaces)?;
    if let Some(sig) = signature.as_deref().filter(|s| !s.fparameters.is_empty()) {
        modifiers::append_type_parameters(cx, buffer, &sig.fparameters, &sig.fbounds)?;
    }
    buffer.push_newline_group(indent, 1);
    let primary = cx
        .kotlin_members()
        .and_then(|m| m.primary_constructor(&class))
        .cloned();
    let mut colon = match primary {
        Some(primary) => primary.write_primary(cx, node, buffer, indent)?,
        None => false,
    };
    if !colon
        && !is_enum
        && !is_interface
        && let Some(ty) = supertype
            .as_ref()
            .filter(|ty| **ty != VarType::VARTYPE_OBJECT)
    {
        let ty = signature.as_ref().map_or(ty, |s| &s.superclass);
        buffer
            .append_possible_newline_or(" ", false)
            .append(": ")
            .append(&get_cast_type_name(cx, ty));
        colon = true;
    }
    if !is_annotation {
        for (index, erased) in interfaces.iter().enumerate() {
            buffer
                .append(if colon { "," } else { " :" })
                .append_possible_newline_or(" ", false);
            colon = true;
            if let Some(ty) = signature
                .as_ref()
                .map_or(Some(erased), |s| s.superinterfaces.get(index))
            {
                buffer.append(&get_cast_type_name(cx, ty));
            }
        }
    }
    buffer.pop_newline_group();
    Ok(())
}

pub(super) fn annotation_definition(
    cx: &mut Cx,
    node: ClassNodeId,
    buffer: &mut TextBuffer,
    indent: i32,
) -> io::Result<()> {
    let class = Arc::clone(&cx.class_nodes[node].class);
    let (removed, container) = members::remove_repeatable(cx, &class)?;
    // The visible attribute is visited first. Exactly these markers were
    // removed from its list by the successive calls to writeAnnotationDefinition.
    let mut remaining = removed;
    annotations::append_except(cx, buffer, indent, class.as_ref(), -1, |annotation| {
        if remaining != 0 && annotation.class_name == "java/lang/annotation/Repeatable" {
            remaining -= 1;
            true
        } else {
            false
        }
    })?;
    annotations::append_jvm(
        buffer,
        indent,
        class.as_ref(),
        true,
        false,
        &class.pool,
        TypeAnnotationData::CLASS_TYPE_PARAMETER,
    )?;
    buffer.append_indent(indent);
    modifiers::append_modifiers(
        buffer,
        class.access_flags,
        modifiers::CLASS_ALLOWED,
        true,
        modifiers::CLASS_EXCLUDED,
    );
    let ty = VarType::from_signature_cl(&class.qualified_name, true);
    buffer
        .append("annotation class ")
        .append(&kotlin_type(cx, Some(&ty), false)?)
        .append_char('(')
        .append_line_separator();
    if let Some(primary) = cx
        .kotlin_members()
        .and_then(|m| m.primary_constructor(&class))
        .cloned()
    {
        let defaults = DefaultArgsMap::for_constructor(cx, node, &primary)?;
        for (index, param) in primary.parameters.iter().enumerate() {
            if index > 0 {
                buffer.append_char(',').append_line_separator();
            }
            buffer
                .append_indent(indent + 1)
                .append("val ")
                .append(&identifier(&param.name))
                .append(": ");
            let mut text = TextBuffer::new(cx);
            param.ty.write(cx, &mut text, indent + 1)?;
            buffer.append_buffer(&text);
            if flags::DECLARES_DEFAULT_VALUE.get(param.flags) {
                buffer.append_buffer(&defaults.render_parameter(cx, index, indent + 1)?);
            }
        }
    }
    buffer
        .append_line_separator()
        .append_indent(indent)
        .append_char(')');
    let mut body = TextBuffer::new(cx);
    let mut has_content = false;
    for id in cx.class_nodes[node].nested.clone() {
        let child = &cx.class_nodes[id];
        if child.kind != ClassKind::Member
            || container.as_ref() == Some(&child.class.qualified_name)
        {
            continue;
        }
        if has_content {
            body.append_line_separator();
        }
        write_class(cx, id, &mut body, indent + 1)?;
        has_content = true;
    }
    if has_content {
        buffer
            .append(" {")
            .append_line_separator()
            .append_buffer(&body)
            .append_indent(indent)
            .append_char('}');
    }
    buffer.append_line_separator();
    Ok(())
}
