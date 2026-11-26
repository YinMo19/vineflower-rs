// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Walk the JVMS type annotation paths as Java type names are written.

use std::io;
use std::iter::successors;

use rustc_hash::FxHashSet;

use super::annotations::render;
use crate::code::code_constants::ACC_STATIC;
use crate::engine::Cx;
use crate::engine::class_nodes::ClassNodeId;
use crate::engine::import_collector::{get_short_name, java_class_name};
use crate::structs::attr::{AnnotationData, PathKind, PathValue, TypeAnnotationData};
use crate::structs::struct_member::Attributes;
use crate::types::{CodeType, GenericType, VarType};
use crate::util::text_buffer::TextBuffer;

pub(super) fn for_target(
    attrs: &Attributes,
    target_type: i32,
    index: i32,
) -> impl Iterator<Item = &TypeAnnotationData> {
    [
        &attrs.runtime_visible_type_annotations,
        &attrs.runtime_invisible_type_annotations,
    ]
    .into_iter()
    .flatten()
    .flat_map(|attribute| &attribute.annotations)
    .filter(move |entry| {
        entry.get_target_type() == target_type && (index < 0 || entry.get_index() == index)
    })
}

struct TypePath<'a> {
    remaining: &'a [PathValue],
    annotation: &'a AnnotationData,
}

/// `ClassWriter.getTypeAnnotations`. Each traversal consumes its own path
/// cursors and shares the original annotation expression identities.
pub(crate) struct TypeAnnotations<'a>(Vec<TypePath<'a>>);

impl<'a> TypeAnnotations<'a> {
    pub(crate) fn for_target(attrs: &'a Attributes, target_type: i32, index: i32) -> Self {
        Self(
            for_target(attrs, target_type, index)
                .map(|entry| TypePath {
                    remaining: &entry.path,
                    annotation: &entry.annotation,
                })
                .collect(),
        )
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    fn step(
        &mut self,
        cx: &mut Cx,
        buffer: &mut TextBuffer,
        filter: &FxHashSet<String>,
        extra_space: bool,
        can_proceed: impl Fn(&PathValue) -> bool,
    ) -> io::Result<()> {
        for entry in &mut self.0 {
            if let Some((first, rest)) = entry.remaining.split_first() {
                if can_proceed(first) {
                    entry.remaining = rest;
                }
            } else if !entry.annotation.was_written() {
                entry.annotation.mark_written();
                let annotation = render(cx, entry.annotation, -1)?;
                if filter.contains(&annotation.convert_to_string_and_allow_data_discard()) {
                    continue;
                }
                if extra_space {
                    buffer.append_char(' ');
                }
                buffer.append_buffer(&annotation).append_char(' ');
            }
        }
        Ok(())
    }

    fn dump_unwritten(&self, cx: &mut Cx, buffer: &mut TextBuffer) -> io::Result<()> {
        let mut any = false;
        for entry in &self.0 {
            if !entry.annotation.was_written() {
                buffer.append(if any { " " } else { "/* " });
                any = true;
                buffer.append_buffer(&render(cx, entry.annotation, -1)?);
                entry.annotation.mark_written();
            }
        }
        if any {
            buffer.append(" */");
        }
        Ok(())
    }
}

/// `TypeAnnotation.appendCastTypeName`.
pub(crate) fn append_cast_type_name(
    cx: &mut Cx,
    buffer: &mut TextBuffer,
    ty: &VarType,
    annotations: &mut TypeAnnotations<'_>,
    filter: &FxHashSet<String>,
    vararg: bool,
    flush: bool,
) -> io::Result<()> {
    // Visit array dimensions first, then emit them after the annotated component.
    let mut dimensions = TextBuffer::new(cx);
    for dimension in 0..ty.array_dim {
        annotations.step(cx, &mut dimensions, filter, true, |path| {
            path.kind == PathKind::DeeperArray
        })?;
        dimensions.append(if vararg && flush && dimension + 1 == ty.array_dim {
            "..."
        } else {
            "[]"
        });
    }

    if ty.ty == CodeType::Object {
        append_object_name(cx, buffer, ty.name(), annotations, filter)?;
        let arguments = ty.arguments();
        if !arguments.is_empty() {
            buffer.append_char('<');
            for (index, argument) in arguments.iter().enumerate() {
                if index > 0 {
                    buffer.append(", ");
                }
                annotations.step(cx, buffer, filter, false, |path| {
                    path.kind == PathKind::GenericArgument
                        && usize::try_from(path.type_arg) == Ok(index)
                })?;
                if argument
                    .as_ref()
                    .is_none_or(|argument| argument.wildcard() != GenericType::WILDCARD_NO)
                {
                    annotations.step(cx, buffer, filter, false, |path| {
                        path.kind == PathKind::OnWildcard
                    })?;
                }
                if let Some(argument) = argument {
                    match argument.wildcard() {
                        GenericType::WILDCARD_EXTENDS => {
                            buffer.append("? extends ");
                        }
                        GenericType::WILDCARD_SUPER => {
                            buffer.append("? super ");
                        }
                        _ => {}
                    }
                    append_cast_type_name(
                        cx,
                        buffer,
                        argument,
                        annotations,
                        filter,
                        vararg,
                        false,
                    )?;
                } else {
                    buffer.append_char('?');
                }
            }
            buffer.append_char('>');
        }
    } else {
        annotations.step(cx, buffer, filter, false, |_| false)?;
        buffer.append_cast_type_name(cx, &ty.resize_array_dim(0));
    }

    buffer.append_buffer(&dimensions);
    if flush {
        annotations.dump_unwritten(cx, buffer)?;
    }
    Ok(())
}

fn append_object_name(
    cx: &mut Cx,
    buffer: &mut TextBuffer,
    name: &str,
    annotations: &mut TypeAnnotations<'_>,
    filter: &FxHashSet<String>,
) -> io::Result<()> {
    let name = java_class_name(cx, name);
    // Register imports even though the annotated name is written one segment at a time.
    get_short_name(cx, &name);
    let classes: Vec<_> = name
        .match_indices('$')
        .map(|(index, _)| &name[..index])
        .chain(std::iter::once(name.as_str()))
        .map(|part| part.replace('.', "/"))
        .collect();
    let outermost_node = cx.class_nodes.id(classes.last().unwrap());
    let start = classes
        .iter()
        .skip(1)
        .map_while(|name| cx.class_nodes.id(name))
        .take_while(|&node| is_static_in_context(cx, node, outermost_node))
        .count();

    for (index, name) in classes.iter().enumerate() {
        if index > 0 {
            buffer.append_char('.');
        }
        if index >= start {
            annotations.step(cx, buffer, filter, false, |path| {
                path.kind == PathKind::DeeperNested
            })?;
        }
        let simple = match cx.class_nodes.get(name) {
            Some(node) => node.simple_name.as_deref().unwrap(),
            None => {
                let tail = name.rsplit('/').next().unwrap();
                tail.split('$').next().unwrap()
            }
        };
        buffer.append_class(simple, false, name);
    }
    Ok(())
}

fn is_static_in_context(cx: &Cx, node: ClassNodeId, outermost_node: Option<ClassNodeId>) -> bool {
    let chain = |start: Option<ClassNodeId>| successors(start, |&id| cx.class_nodes[id].parent);
    let is_static = |id: ClassNodeId| cx.class_nodes[id].access & ACC_STATIC != 0;
    if chain(outermost_node).any(is_static) {
        let current = cx
            .current_class_node
            .as_deref()
            .and_then(|name| cx.class_nodes.id(name));
        if chain(current).any(|id| id == node) {
            return true;
        }
    }
    is_static(node)
}

/// `ClassWriter.appendTypeParameters` for class and method signatures.
pub(in crate::engine) fn append_type_parameters(
    cx: &mut Cx,
    buffer: &mut TextBuffer,
    parameters: &[String],
    bounds: &[Vec<VarType>],
) {
    buffer.append_char('<');
    for (index, (parameter, bounds)) in parameters.iter().zip(bounds).enumerate() {
        if index > 0 {
            buffer.append(", ");
        }
        buffer.append(parameter);
        if let Some((first, rest)) = bounds.split_first()
            && (!rest.is_empty() || first.value.as_deref() != Some("java/lang/Object"))
        {
            buffer.append(" extends ").append_cast_type_name(cx, first);
            for bound in rest {
                buffer.append(" & ").append_cast_type_name(cx, bound);
            }
        }
    }
    buffer.append_char('>');
}
