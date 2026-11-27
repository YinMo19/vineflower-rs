//! ClassWriter.writeClassDefinition, including the type signatures shared with members.

use std::{io, sync::Arc};

use super::{annotations, javadoc, record_components, type_annotations};
use crate::code::code_constants::*;
use crate::engine::{
    Cx,
    class_nodes::{ClassKind, ClassNodeId},
};
use crate::structs::{Attributes, StructClass, StructMember};
use crate::types::{GenericClassDescriptor, VarType};
use crate::util::text_buffer::TextBuffer;

/// Write a class declaration through its opening brace. The surrounding
/// ClassWriter supplies the body and the final newline of an anonymous class.
pub fn write_class_definition(
    cx: &mut Cx,
    node: ClassNodeId,
    buffer: &mut TextBuffer,
    indent: i32,
) -> io::Result<()> {
    cx.with_class_node(node, |cx| append_definition(cx, node, buffer, indent))
}

pub(super) fn append_definition(
    cx: &mut Cx,
    node: ClassNodeId,
    buffer: &mut TextBuffer,
    indent: i32,
) -> io::Result<()> {
    let node = &cx.class_nodes[node];
    let class = Arc::clone(&node.class);
    let kind = node.kind;
    let name = node.simple_name.clone();
    let mark = cx.options.mark_corresponding_synthetics;
    if kind == ClassKind::Anonymous {
        if mark {
            append_synthetic_class_comment(buffer, &class);
        }
        buffer.append(" {");
        return Ok(());
    }

    let mut flags = if kind == ClassKind::Root {
        class.access_flags
    } else {
        node.access
    };
    let synthetic = flags & ACC_SYNTHETIC != 0 || class.attributes.synthetic.is_some();
    let is_enum = flags & ACC_ENUM != 0 && cx.options.decompile_enums;
    let is_interface = flags & ACC_INTERFACE != 0;
    let is_annotation = flags & ACC_ANNOTATION != 0;
    let permitted = class
        .attributes
        .permitted_subclasses
        .as_ref()
        .map_or(&[][..], |a| a.classes.as_slice());
    let sealed = !permitted.is_empty();
    let non_sealed = !sealed
        && flags & ACC_FINAL == 0
        && class.version.has_sealed_classes()
        && inherits_sealed(cx, &class);
    let components = class.get_record_components();
    if kind == ClassKind::Member
        && node
            .parent
            .is_some_and(|p| cx.class_nodes[p].class.has_modifier(ACC_INTERFACE))
    {
        flags &= !(ACC_PUBLIC | ACC_STATIC);
    }

    append_class_comments(cx, buffer, &class, synthetic, indent)?;
    annotations::append_annotations(cx, buffer, &class.attributes, indent, -1)?;
    buffer.append_indent(indent);
    if is_enum {
        flags &= !(ACC_ABSTRACT | ACC_FINAL);
        if matches!(kind, ClassKind::Member | ClassKind::Local) {
            flags &= !ACC_STATIC;
        }
    }
    if components.is_some() {
        flags &= !(ACC_STATIC | ACC_FINAL);
    }
    let allowed = ACC_PUBLIC
        | ACC_PROTECTED
        | ACC_PRIVATE
        | ACC_ABSTRACT
        | ACC_STATIC
        | ACC_FINAL
        | ACC_STRICT;
    let implicit = if is_interface {
        ACC_ABSTRACT | ACC_STATIC
    } else {
        0
    };
    append_modifiers(buffer, flags & allowed & !implicit);
    if sealed && !is_enum {
        buffer.append("sealed ");
    } else if non_sealed {
        buffer.append("non-sealed ");
    }
    if is_enum {
        buffer.append("enum ");
    } else if is_interface {
        buffer.append(if is_annotation {
            "@interface "
        } else {
            "interface "
        });
    } else if let Some(module) = class
        .attributes
        .module
        .as_ref()
        .filter(|_| flags & ACC_MODULE != 0)
    {
        if module.module_flags & ACC_OPEN != 0 {
            buffer.append("open ");
        }
        buffer.append("module ").append(&module.module_name);
    } else {
        buffer.append(if components.is_some() {
            "record "
        } else {
            "class "
        });
    }
    let name = name.ok_or_else(|| {
        io::Error::new(io::ErrorKind::InvalidData, "missing class declaration name")
    })?;
    buffer.append_class(&name, true, &class.qualified_name);

    let supertype = class
        .super_class
        .as_ref()
        .map(|c| VarType::from_signature_cl(c.get_string(), true));
    let interfaces: Vec<_> = class
        .interface_names
        .iter()
        .map(|s| VarType::from_signature_cl(s, true))
        .collect();
    let signature = verify_class_signature(cx, &class, supertype.as_ref(), &interfaces)?;
    if let Some(sig) = signature.as_deref().filter(|s| !s.fparameters.is_empty()) {
        type_annotations::append_type_parameters(cx, buffer, &sig.fparameters, &sig.fbounds);
    }
    if let Some(components) = components {
        buffer.append_char('(');
        record_components::append_components(cx, buffer, &class, components, indent)?;
        buffer.append_char(')');
    }

    buffer.push_newline_group(indent, 1);
    if !is_enum
        && !is_interface
        && components.is_none()
        && let Some(supertype) = supertype.filter(|ty| ty != &VarType::VARTYPE_OBJECT)
    {
        buffer
            .append_possible_newline_or(" ", false)
            .append("extends ")
            .append_cast_type_name(cx, signature.as_ref().map_or(&supertype, |s| &s.superclass));
    }
    if !is_annotation && !interfaces.is_empty() {
        buffer
            .append_possible_newline_or(" ", false)
            .append(if is_interface {
                "extends "
            } else {
                "implements "
            });
        for (i, erased) in interfaces.iter().enumerate() {
            if i > 0 {
                buffer
                    .append_char(',')
                    .append_possible_newline_or(" ", false);
            }
            if let Some(ty) = signature
                .as_ref()
                .map_or(Some(erased), |s| s.superinterfaces.get(i))
            {
                buffer.append_cast_type_name(cx, ty);
            }
        }
    }
    if sealed && !is_enum {
        buffer
            .append_possible_newline_or(" ", false)
            .append("permits ");
        for (i, name) in permitted.iter().enumerate() {
            if i > 0 {
                buffer
                    .append_char(',')
                    .append_possible_newline_or(" ", false);
            }
            buffer.append_cast_type_name(cx, &VarType::from_signature_cl(name, true));
        }
    }
    buffer.pop_newline_group();
    if mark && kind == ClassKind::Local {
        append_synthetic_class_comment(buffer, &class);
    }
    buffer.append(" {").append_line_separator();
    Ok(())
}

fn append_class_comments(
    cx: &mut Cx,
    buffer: &mut TextBuffer,
    class: &StructClass,
    synthetic: bool,
    indent: i32,
) -> io::Result<()> {
    append_deprecation(buffer, &class.attributes, indent);
    let old = cx
        .pool_interceptor
        .as_ref()
        .and_then(|pool| pool.get_old_name(&class.qualified_name))
        .map(str::to_owned);
    super::comments::append_rename_comment(
        cx,
        buffer,
        old.as_deref(),
        super::comments::RenameKind::Class,
        indent,
    )?;
    if synthetic {
        super::comments::append_comment(buffer, "synthetic class", indent);
    }
    if let Some(provider) = &cx.javadoc {
        let style = provider.class_style(class);
        if let Some(doc) = provider.class_doc(class) {
            javadoc::append(buffer, style, &doc, indent);
        }
    }
    Ok(())
}

pub(super) fn append_modifiers(buffer: &mut TextBuffer, flags: i32) {
    for (flag, keyword) in [
        (ACC_PUBLIC, "public"),
        (ACC_PROTECTED, "protected"),
        (ACC_PRIVATE, "private"),
        (ACC_ABSTRACT, "abstract"),
        (ACC_STATIC, "static"),
        (ACC_FINAL, "final"),
        (ACC_STRICT, "strictfp"),
        (ACC_TRANSIENT, "transient"),
        (ACC_VOLATILE, "volatile"),
        (ACC_SYNCHRONIZED, "synchronized"),
        (ACC_NATIVE, "native"),
    ] {
        if flags & flag != 0 {
            buffer.append(keyword).append_char(' ');
        }
    }
}

pub(crate) fn append_deprecation(buffer: &mut TextBuffer, attrs: &Attributes, indent: i32) {
    if attrs.deprecated.is_some()
        && !annotations::declaration_annotations(attrs)
            .any(|a| a.class_name == "java/lang/Deprecated")
    {
        buffer
            .append_indent(indent)
            .append("/** @deprecated */")
            .append_line_separator();
    }
}

fn append_synthetic_class_comment(buffer: &mut TextBuffer, class: &StructClass) {
    let name = class.qualified_name.rsplit('/').next().unwrap();
    buffer
        .append(" /* ")
        .append_class(name, true, &class.qualified_name)
        .append(" */");
}

fn inherits_sealed(cx: &Cx, class: &StructClass) -> bool {
    class
        .super_class
        .iter()
        .map(|c| c.get_string())
        .chain(&class.interface_names)
        .filter_map(|name| cx.classes().get_class(name))
        .any(|parent| parent.attributes.permitted_subclasses.is_some())
}

pub(crate) fn verify_class_signature(
    cx: &Cx,
    class: &StructClass,
    supertype: Option<&VarType>,
    interfaces: &[VarType],
) -> io::Result<Option<Arc<GenericClassDescriptor>>> {
    let Some(signature) = class.shared_signature() else {
        return Ok(None);
    };
    let supertype = supertype.ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            "class signature without superclass",
        )
    })?;
    signature.update(|s| s.verify_types(cx, supertype, interfaces));
    Ok(Some(signature.get()))
}
