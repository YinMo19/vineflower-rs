// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Write annotation expressions while preserving import and token positions.

use std::io;

use rustc_hash::FxHashSet;

use crate::decompiler::exps::literal;
use crate::engine::Cx;
use crate::engine::import_collector::{get_short_name, java_class_name};
use crate::structs::attr::{AnnotationData, AnnotationElement, ElementValue, TypeAnnotationData};
use crate::structs::consts::ConstantValue;
use crate::structs::struct_member::Attributes;
use crate::types::{CodeType, TypeFamily, VarType};
use crate::util::text_buffer::TextBuffer;

use super::type_annotations;

pub(super) fn declaration_annotations(attrs: &Attributes) -> impl Iterator<Item = &AnnotationData> {
    [
        &attrs.runtime_visible_annotations,
        &attrs.runtime_invisible_annotations,
    ]
    .into_iter()
    .flatten()
    .flat_map(|attribute| &attribute.annotations)
}

pub(super) fn parameter_annotations(
    attrs: &Attributes,
    parameter: usize,
) -> impl Iterator<Item = &AnnotationData> {
    [
        &attrs.runtime_visible_parameter_annotations,
        &attrs.runtime_invisible_parameter_annotations,
    ]
    .into_iter()
    .flatten()
    .filter_map(move |attribute| attribute.param_annotations.get(parameter))
    .flatten()
}

pub(super) fn append_annotations(
    cx: &mut Cx,
    buffer: &mut TextBuffer,
    attrs: &Attributes,
    indent: i32,
    target_type: i32,
) -> io::Result<FxHashSet<String>> {
    let mut filter = FxHashSet::default();
    for annotation in declaration_annotations(attrs) {
        annotation.mark_written();
        buffer.append_indent(indent);
        filter.insert(render(cx, annotation, -1)?.convert_to_string_and_allow_data_discard());
        buffer.append_buffer(&render(cx, annotation, indent)?);
        finish_annotation(buffer, indent);
    }

    if !matches!(
        target_type,
        TypeAnnotationData::FIELD | TypeAnnotationData::METHOD_RETURN_TYPE
    ) {
        append_top_level_type_annotations(cx, buffer, attrs, indent, target_type, -1, &filter)?;
    }
    Ok(filter)
}

fn append_top_level_type_annotations(
    cx: &mut Cx,
    buffer: &mut TextBuffer,
    attrs: &Attributes,
    indent: i32,
    target_type: i32,
    index: i32,
    filter: &FxHashSet<String>,
) -> io::Result<()> {
    for entry in
        type_annotations::for_target(attrs, target_type, index).filter(|entry| entry.is_top_level())
    {
        let annotation = &entry.annotation;
        let single_line = render(cx, annotation, -1)?.convert_to_string_and_allow_data_discard();
        if !filter.contains(&single_line) {
            buffer.append_indent(indent);
            buffer.append_buffer(&render(cx, annotation, indent)?);
            finish_annotation(buffer, indent);
        }
    }
    Ok(())
}

fn finish_annotation(buffer: &mut TextBuffer, indent: i32) {
    if indent < 0 {
        buffer.append_char(' ');
    } else {
        buffer.append_line_separator();
    }
}

pub(super) fn render(
    cx: &mut Cx,
    annotation: &AnnotationData,
    indent: i32,
) -> io::Result<TextBuffer> {
    let mut buffer = TextBuffer::new(cx);
    let owner = annotation.class_name.as_str();
    let qualified_name = java_class_name(cx, owner);
    let name = get_short_name(cx, &qualified_name);
    buffer.append_char('@').append_all_classes(&name, owner);

    if annotation.par_names.is_empty() {
        return Ok(buffer);
    }
    let single_element = annotation.par_names.as_slice() == ["value"];
    buffer
        .append_char('(')
        .push_newline_group(indent, 1)
        .append_possible_newline();
    for (index, name) in annotation.par_names.iter().enumerate() {
        let value = &annotation.par_values[index].value;
        if !single_element {
            let declared = cx.classes().get_class(owner).and_then(|class| {
                class
                    .methods
                    .iter()
                    .find(|method| method.name == *name)
                    .map(|method| method.descriptor.clone())
            });
            if let Some(descriptor) = declared {
                buffer.append_method(name, false, owner, name, &descriptor);
            } else {
                let descriptor = format!("(){}", element_type(value));
                buffer.append_method(name, false, owner, name, &descriptor);
            }
            buffer.append(" = ");
        }

        let value = match value {
            ElementValue::Array(elements) => match elements.as_slice() {
                [element] if !matches!(element.value, ElementValue::Array(_)) => &element.value,
                _ => value,
            },
            _ => value,
        };
        buffer.append_buffer(&render_element(cx, value, indent)?);
        if index + 1 < annotation.par_names.len() {
            buffer
                .append_char(',')
                .append_possible_newline_or(" ", false);
        } else {
            buffer.append_possible_newline_or("", true);
        }
    }
    buffer.append_char(')').pop_newline_group();
    Ok(buffer)
}

pub(super) fn render_element(
    cx: &mut Cx,
    value: &ElementValue,
    indent: i32,
) -> io::Result<TextBuffer> {
    match value {
        ElementValue::Const { ty, value } => literal::render(cx, ty, value, None, false),
        ElementValue::Class(name) => literal::render(
            cx,
            &VarType::VARTYPE_CLASS,
            &ConstantValue::String(name.clone().into()),
            None,
            false,
        ),
        ElementValue::EnumConstant {
            const_name,
            descriptor,
        } => Ok(literal::static_field(
            cx,
            descriptor.ty.name(),
            const_name,
            descriptor,
            None,
        )),
        ElementValue::Annotation(annotation) => render(cx, annotation, indent),
        ElementValue::Array(elements) => render_array(cx, elements, indent),
    }
}

fn render_array(
    cx: &mut Cx,
    elements: &[AnnotationElement],
    indent: i32,
) -> io::Result<TextBuffer> {
    let mut buffer = TextBuffer::new(cx);
    buffer.append_char('{');
    if let Some(first) = elements.first() {
        let expected = element_type(&first.value).resize_array_dim(0);
        buffer
            .push_newline_group(indent, 2)
            .append_possible_newline()
            .push_newline_group(indent, 0);
        for (index, element) in elements.iter().enumerate() {
            if index > 0 {
                buffer
                    .append_char(',')
                    .append_possible_newline_or(" ", false);
            }
            append_array_element(cx, &mut buffer, &element.value, &expected, indent)?;
        }
        buffer
            .pop_newline_group()
            .append_possible_newline_or("", true)
            .pop_newline_group();
    }
    buffer.append_char('}');
    Ok(buffer)
}

fn append_array_element(
    cx: &mut Cx,
    buffer: &mut TextBuffer,
    value: &ElementValue,
    expected: &VarType,
    indent: i32,
) -> io::Result<()> {
    let actual = element_type(value);
    if !expected.higher_equal_in_lattice_than(cx, &actual)
        && (actual == VarType::VARTYPE_OBJECT || expected.ty != CodeType::Object)
    {
        buffer
            .append_char('(')
            .append_cast_type_name(cx, expected)
            .append_char(')');
    }
    let text = match value {
        ElementValue::Const { ty, value }
            if ty.type_family == TypeFamily::Integer
                && (*expected == VarType::VARTYPE_INT || *expected == VarType::VARTYPE_INTEGER) =>
        {
            literal::render(cx, &VarType::VARTYPE_INT, value, None, false)?
        }
        _ => render_element(cx, value, indent)?,
    };
    buffer.append_buffer(&text);
    Ok(())
}

fn element_type(value: &ElementValue) -> VarType {
    match value {
        ElementValue::EnumConstant { descriptor, .. } => descriptor.ty.clone(),
        ElementValue::Class(_) => VarType::VARTYPE_CLASS,
        ElementValue::Annotation(_) => VarType::VARTYPE_VOID,
        ElementValue::Array(elements) => elements
            .first()
            .map_or(VarType::VARTYPE_OBJECT, |first| element_type(&first.value))
            .resize_array_dim(1),
        ElementValue::Const { ty, .. } => ty.clone(),
    }
}
