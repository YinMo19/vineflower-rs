// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! RecordHelper's declaration of the record components in a class header.

use super::{annotations, type_annotations::TypeAnnotations};
use crate::code::code_constants::ACC_VARARGS;
use crate::engine::Cx;
use crate::structs::{
    StructClass, StructMember, StructMethod, StructRecordComponent, attr::TypeAnnotationData,
};
use crate::types::VarType;
use crate::util::text_buffer::TextBuffer;
use rustc_hash::FxHashSet;
use std::{io, sync::Arc};

pub(super) fn append_components(
    cx: &mut Cx,
    buffer: &mut TextBuffer,
    class: &StructClass,
    components: &[StructRecordComponent],
    indent: i32,
) -> io::Result<()> {
    let constructor = super::records::canonical_constructor(class, components).map(Arc::as_ref);
    let varargs = constructor.is_some_and(|c| c.has_modifier(ACC_VARARGS));
    buffer
        .push_newline_group(indent, 1)
        .append_possible_newline()
        .push_newline_group(indent, 0);
    for (i, component) in components.iter().enumerate() {
        if i > 0 {
            buffer
                .append_char(',')
                .append_possible_newline_or(" ", false);
        }
        let written = append_annotations(cx, buffer, class, component, constructor, i)?;
        let erased = VarType::from_signature(&component.descriptor);
        let mut ty = component.verified_type(cx, class, &erased);
        let vararg = varargs && i + 1 == components.len();
        if vararg {
            ty = ty.decrease_array_dim();
        }
        let mut type_annotations =
            TypeAnnotations::for_target(&component.attributes, TypeAnnotationData::FIELD, -1);
        if type_annotations.is_empty() {
            buffer.append_cast_type_name(cx, &ty);
        } else {
            buffer.append_annotated_cast_type_name(
                cx,
                &ty,
                &mut type_annotations,
                &written,
                false,
                true,
            )?;
        }
        if vararg {
            buffer.append("...");
        }
        buffer.append_char(' ').append_field(
            &component.name,
            true,
            &class.qualified_name,
            &component.name,
            &component.descriptor,
        );
    }
    buffer
        .pop_newline_group()
        .append_possible_newline_or("", true)
        .pop_newline_group();
    Ok(())
}

fn append_annotations(
    cx: &mut Cx,
    buffer: &mut TextBuffer,
    class: &StructClass,
    component: &StructRecordComponent,
    constructor: Option<&StructMethod>,
    index: usize,
) -> io::Result<FxHashSet<String>> {
    let getter = class.get_method(&component.name, &format!("(){}", component.descriptor));
    let declared = std::iter::once(&component.attributes)
        .chain(getter.map(|m| &m.attributes))
        .flat_map(annotations::declaration_annotations);
    let on_parameter = constructor
        .into_iter()
        .flat_map(|m| annotations::parameter_annotations(&m.attributes, index));
    let mut written = FxHashSet::default();
    for annotation in declared.chain(on_parameter) {
        let text = annotations::render(cx, annotation, -1)?;
        if written.insert(text.convert_to_string_and_allow_data_discard()) {
            buffer.append_buffer(&text).append_char(' ');
        }
    }
    Ok(written)
}
