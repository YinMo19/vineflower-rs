//! ClassWriter.writeField. Initializer expressions still belong to their
//! constructors and class initializer, including their bytecode mappings.

use super::{
    annotations,
    comments::{self, RenameKind},
    declaration, javadoc,
    type_annotations::TypeAnnotations,
};
use crate::code::code_constants::*;
use crate::decompiler::exps::{
    ExprKind, WriteFlags, literal,
    write::{
        self,
        casts::{CastOptions, append_casted},
    },
};
use crate::engine::{Cx, class_nodes::ClassNodeId};
use crate::structs::{StructField, StructMember, attr::TypeAnnotationData};
use crate::types::VarType;
use crate::util::{interpreter_util::make_unique_key, text_buffer::TextBuffer};
use std::{io, sync::Arc};

pub(super) fn write_field(
    cx: &mut Cx,
    node: ClassNodeId,
    field: &StructField,
    buffer: &mut TextBuffer,
    indent: i32,
) -> io::Result<()> {
    let class = Arc::clone(&cx.class_nodes[node].class);
    let component = class.get_record_components().is_some_and(|items| {
        items
            .iter()
            .any(|c| c.name == field.name && c.descriptor == field.descriptor)
    });
    if component && !field.has_modifier(ACC_STATIC) {
        return Ok(());
    }
    let is_enum = field.has_modifier(ACC_ENUM) && cx.options.decompile_enums;
    declaration::append_deprecation(buffer, &field.attributes, indent);
    let mut name = field.name.to_string();
    if let Some(pool) = &cx.pool_interceptor {
        let key = format!("{} {} {}", class.qualified_name, name, field.descriptor);
        if let Some(renamed) = pool.get_name(&key) {
            name = renamed
                .split(' ')
                .nth(1)
                .ok_or_else(|| {
                    io::Error::new(io::ErrorKind::InvalidData, "Invalid renamed field entry")
                })?
                .to_owned();
        }
        let key = format!("{} {} {}", class.qualified_name, name, field.descriptor);
        let old = pool.get_old_name(&key).map(str::to_owned);
        comments::append_rename_comment(cx, buffer, old.as_deref(), RenameKind::Field, indent)?;
    }
    if field.is_synthetic() {
        comments::append_comment(buffer, "synthetic field", indent);
    }
    if let Some(provider) = &cx.javadoc {
        let style = provider.field_style(&class, field);
        if let Some(doc) = provider.field_doc(&class, field) {
            javadoc::append(buffer, style, &doc, indent);
        }
    }
    let written = annotations::append_annotations(
        cx,
        buffer,
        &field.attributes,
        indent,
        TypeAnnotationData::FIELD,
    )?;
    buffer.append_indent(indent);
    if !is_enum {
        let allowed = ACC_PUBLIC
            | ACC_PROTECTED
            | ACC_PRIVATE
            | ACC_STATIC
            | ACC_FINAL
            | ACC_TRANSIENT
            | ACC_VOLATILE;
        let implied = if class.has_modifier(ACC_INTERFACE) {
            ACC_PUBLIC | ACC_STATIC | ACC_FINAL
        } else {
            0
        };
        declaration::append_modifiers(buffer, field.access_flags & allowed & !implied);
    }
    let erased = VarType::from_signature(&field.descriptor);
    let ty = field.verified_type(cx, &class, &erased);
    if !is_enum {
        let mut paths =
            TypeAnnotations::for_target(&field.attributes, TypeAnnotationData::FIELD, -1);
        if paths.is_empty() {
            buffer.append_cast_type_name(cx, &ty);
        } else {
            buffer.append_annotated_cast_type_name(cx, &ty, &mut paths, &written, false, true)?;
        }
        buffer.append_char(' ');
    }
    buffer.append_field(&name, true, &class.qualified_name, &name, &field.descriptor);
    let wrapper = cx.class_nodes[node]
        .wrapper
        .as_ref()
        .expect("class writer requires a published wrapper");
    let initializers = if field.has_modifier(ACC_STATIC) {
        &wrapper.static_field_initializers
    } else {
        &wrapper.dynamic_field_initializers
    };
    if let Some(&expr) = initializers.get_with_key(&make_unique_key(&field.name, &field.descriptor))
    {
        if is_enum && matches!(cx.ir[expr].kind, ExprKind::New { .. }) {
            cx.ir[expr].write_flags.insert(WriteFlags::ENUM_CONST);
            buffer.append_buffer(&write::to_java(cx, expr, indent)?);
        } else {
            buffer.append(" = ");
            literal::adjust_const_type(&mut cx.ir, expr, &erased);
            append_casted(cx, expr, &ty, buffer, indent, CastOptions::default())?;
        }
    } else if field.has_modifier(ACC_STATIC | ACC_FINAL)
        && let Some(attr) = &field.attributes.constant_value
    {
        let constant = class
            .pool
            .get_primitive_constant(attr.index)
            .ok_or_else(|| {
                io::Error::new(io::ErrorKind::InvalidData, "Missing field constant value")
            })?;
        cx.expression_ids.next();
        buffer.append(" = ").append_buffer(&literal::render(
            cx,
            &erased,
            &constant.value,
            None,
            false,
        )?);
    }
    if !is_enum {
        buffer.append_char(';').append_line_separator();
    }
    Ok(())
}
