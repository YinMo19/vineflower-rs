// SPDX-License-Identifier: Apache-2.0

use std::{io, sync::Arc};

use super::{declaration, fallback, lambda};
use crate::{
    code::code_constants::*,
    engine::{
        Cx,
        class_nodes::{ClassKind, ClassNodeId},
        class_wrapper::{MethodSlot, catch_method_failure},
        class_writer::{self, comments::append_comment},
    },
    kotlin::{
        declarations::resolve,
        imports,
        members::{self, ClassElement, FieldElement, KProperty, MethodElement},
        metadata::{flags, proto::class::Kind},
    },
    structs::{StructClass, StructMember, StructMethod},
    util::{interpreter_util::make_unique_key, text_buffer::TextBuffer},
};
use rustc_hash::FxHashSet;

pub fn write_class(
    cx: &mut Cx,
    node: ClassNodeId,
    buffer: &mut TextBuffer,
    indent: i32,
) -> io::Result<()> {
    cx.with_class_node(node, |cx| write_current_class(cx, node, buffer, indent))
}

fn write_current_class(
    cx: &mut Cx,
    node: ClassNodeId,
    buffer: &mut TextBuffer,
    indent: i32,
) -> io::Result<()> {
    cx.imports = imports::from_parent(&cx.imports);
    let class = cx.class_nodes[node].class.clone();
    if cx.class_nodes[node].wrapper.is_none() {
        buffer
            .append("/* $VF: Couldn't be decompiled. Class ")
            .append(&class.qualified_name)
            .append(" wasn't processed yet! */");
        for line in cx
            .options
            .error_message
            .split('\n')
            .filter(|s| !s.is_empty())
        {
            buffer.append("// ").append(line).append_line_separator();
        }
        return Ok(());
    }
    if let Err(error) = catch_method_failure(|| prepare_class(cx, node)) {
        if error.kind() == io::ErrorKind::Interrupted {
            return Err(error);
        }
        log::warn!(
            "Class {} couldn't be written: {error}",
            class.qualified_name
        );
        class_writer::write_exception(cx, buffer, &error);
        return Ok(());
    }
    members::parse_metadata_for(cx, &class);
    let data = cx.kotlin_members().and_then(|m| m.class(&class)).cloned();
    if let Some(ClassElement::MultifileFacade(parts)) = &data {
        let note = " * This is a multifile facade. The actual implementations of the functions are in the following files:";
        buffer.append("/*").append_line_separator().append(note).append_line_separator();
        for part in parts {
            buffer
                .append(" * ")
                .append(part.as_utf8_lossy())
                .append_line_separator();
        }
        buffer.append(" */").append_line_separator();
        if !cx.options.kt_decompile_facades {
            return Ok(());
        }
    }
    let kflags = match &data {
        Some(ClassElement::Class(cls)) => cls.proto.flags(),
        None => {
            append_comment(buffer, "Class flags could not be determined", indent);
            0
        }
        _ => 0,
    };
    if cx.options.sourcefile_comments
        && let Some(attr) = &class.attributes.source_file
    {
        buffer
            .append_indent(indent)
            .append("// $VF: Compiled from ")
            .append(&attr.get_source_file(&class.pool))
            .append_line_separator();
    }
    if flags::CLASS_KIND.get(kflags) == Some(Kind::AnnotationClass)
        || class.has_modifier(ACC_ANNOTATION)
    {
        return declaration::annotation_definition(cx, node, buffer, indent);
    }
    match &data {
        Some(ClassElement::Synthetic(function)) => {
            return lambda::write_lambda(cx, node, buffer, indent, Some(function));
        }
        Some(ClassElement::FailedLambda) => {
            return lambda::write_lambda(cx, node, buffer, indent, None);
        }
        _ => {}
    }
    let companion = companion_node(cx, node, data.as_ref())?;
    let file = matches!(data, Some(ClassElement::File(_)));
    if !file {
        declaration::definition(cx, node, buffer, indent, data.as_ref(), kflags)?;
    }
    let level = if file { indent } else { indent + 1 };
    let mut body = Body {
        buffer: TextBuffer::new(cx),
        visited: FxHashSet::default(),
        has_content: false,
    };
    body.fields(cx, node, &class, level)?;
    body.methods(cx, node, &class, companion, file, level)?;
    for child in cx.class_nodes[node].nested.clone() {
        let nested = &cx.class_nodes[child];
        if nested.kind == ClassKind::Member
            && !(cx.options.remove_synthetic
                && (nested.access & ACC_SYNTHETIC != 0 || nested.class.is_synthetic()))
            && !cx.class_nodes[node]
                .hidden_members
                .contains(nested.class.qualified_name.as_str())
        {
            body.separate();
            write_class(cx, child, &mut body.buffer, level)?;
        }
    }
    if file {
        buffer.append_buffer(&body.buffer);
    } else {
        if !body.buffer.contains_only_whitespaces() {
            buffer
                .append(" {")
                .append_line_separator()
                .append_buffer(&body.buffer)
                .append_indent(indent)
                .append_char('}');
        }
        if cx.class_nodes[node].kind != ClassKind::Anonymous {
            buffer.append_line_separator();
        }
    }
    Ok(())
}

fn prepare_class(cx: &mut Cx, node: ClassNodeId) -> io::Result<()> {
    class_writer::prepare_initializers_and_enums(cx, node)?;
    let class = cx.class_nodes[node].class.clone();
    if cx.options.decompile_enums && class.has_modifier(ACC_ENUM) {
        cx.class_nodes[node].hidden_members.extend(
            class
                .fields
                .iter()
                .filter(|f| f.is_synthetic() && f.descriptor == "Lkotlin/enums/EnumEntries;")
                .map(|f| make_unique_key(&f.name, &f.descriptor)),
        );
    }
    members::process_objects(cx, node)
}

fn companion_node(
    cx: &Cx,
    node: ClassNodeId,
    data: Option<&ClassElement>,
) -> io::Result<Option<ClassNodeId>> {
    let Some(ClassElement::Class(class)) = data else {
        return Ok(None);
    };
    let Some(id) = class.proto.companion_object_name else {
        return Ok(None);
    };
    let names = class
        .names
        .as_ref()
        .ok_or_else(|| io::Error::other("Missing Kotlin companion name resolver"))?;
    let name = resolve(names, id)?;
    Ok(cx.class_nodes[node]
        .nested
        .iter()
        .copied()
        .find(|&id| cx.class_nodes[id].simple_name.as_ref() == Some(&name)))
}

struct Body {
    buffer: TextBuffer,
    // The getter, setter and backing field share the same bound KProperty.
    visited: FxHashSet<*const KProperty>,
    has_content: bool,
}

impl Body {
    fn separate(&mut self) {
        if self.has_content {
            self.buffer.append_line_separator();
        }
        self.has_content = true;
    }

    fn fields(
        &mut self,
        cx: &mut Cx,
        node: ClassNodeId,
        class: &Arc<StructClass>,
        indent: i32,
    ) -> io::Result<()> {
        let fields: Vec<_> = cx.kotlin_members().map_or_else(
            || class.fields.iter().cloned().collect(),
            |m| m.fields(class).cloned().collect(),
        );
        let mut enums = false;
        let decompile_enums = cx.options.decompile_enums;
        for field in fields
            .iter()
            .filter(|f| decompile_enums && f.has_modifier(ACC_ENUM))
        {
            if enums {
                self.buffer.append_char(',').append_line_separator();
            }
            let mut text = TextBuffer::new(cx);
            fallback::write_field(cx, node, field, &mut text, indent)?;
            let key = if field.has_modifier(ACC_STATIC) {
                "<clinit> ()V"
            } else {
                "<init> ()V"
            };
            self.buffer
                .append_buffer_for(&text, Some(&class.qualified_name), Some(key));
            enums = true;
            self.has_content = true;
        }
        let primary = cx
            .kotlin_members()
            .and_then(|m| m.primary_constructor(class));
        let constructor = match primary {
            Some(primary) => make_unique_key(
                INIT_NAME,
                &primary
                    .method
                    .as_ref()
                    .ok_or_else(|| io::Error::other("Primary constructor has no JVM method"))?
                    .descriptor,
            ),
            None => "<init> ()V".into(),
        };
        let mut trailing_newline = false;
        for field in fields {
            if enums {
                self.buffer
                    .append_char(';')
                    .append_line_separator()
                    .append_line_separator();
                enums = false;
                trailing_newline = true;
            }
            if field.has_modifier(ACC_ENUM) {
                continue;
            }
            let initializer = if field.has_modifier(ACC_STATIC) {
                "<clinit> ()V"
            } else {
                &constructor
            };
            let element = cx.kotlin_members().and_then(|m| m.field(&field)).cloned();
            let mut text = TextBuffer::new(cx);
            match element {
                Some(FieldElement::Property(property)) => {
                    if !Arc::ptr_eq(&property.class, class)
                        || !self.visited.insert(Arc::as_ptr(&property))
                    {
                        continue;
                    }
                    property.write(cx, node, &mut text, indent)?;
                    let multiline = text.count_lines() > 0;
                    if multiline && self.has_content && !trailing_newline {
                        self.buffer.append_line_separator();
                    }
                    self.buffer
                        .append_buffer_for(&text, Some(&class.qualified_name), Some(initializer))
                        .append_line_separator();
                    if multiline {
                        self.buffer.append_line_separator();
                    }
                    trailing_newline = multiline;
                }
                Some(FieldElement::Hidden(_)) => continue,
                None => {
                    if cx.options.remove_synthetic && field.is_synthetic()
                        || cx.class_nodes[node]
                            .hidden_members
                            .contains(make_unique_key(&field.name, &field.descriptor).as_str())
                        || field.access_flags == (ACC_FINAL | ACC_PRIVATE)
                            && class.get_record_components().is_some_and(|items| {
                                items.iter().any(|c| {
                                    c.name == field.name && c.descriptor == field.descriptor
                                })
                            })
                    {
                        continue;
                    }
                    log::warn!(
                        "Non-enum field {} is not associated with Kotlin property",
                        field.name
                    );
                    fallback::write_field(cx, node, &field, &mut text, indent)?;
                    self.buffer.append_buffer_for(
                        &text,
                        Some(&class.qualified_name),
                        Some(initializer),
                    );
                    trailing_newline = false;
                }
            }
            self.has_content = true;
        }
        if trailing_newline {
            self.buffer
                .set_length(self.buffer.length() - cx.options.line_separator().len() as i32);
        }
        Ok(())
    }

    fn methods(
        &mut self,
        cx: &mut Cx,
        node: ClassNodeId,
        class: &Arc<StructClass>,
        companion: Option<ClassNodeId>,
        file: bool,
        indent: i32,
    ) -> io::Result<()> {
        let methods: Vec<_> = cx.kotlin_members().map_or_else(
            || class.methods.iter().cloned().collect(),
            |m| m.methods(class).cloned().collect(),
        );
        for (index, method) in methods.iter().enumerate() {
            let key = make_unique_key(&method.name, &method.descriptor);
            if hidden_method(cx, node, companion, method, &key) {
                continue;
            }
            let element = cx.kotlin_members().and_then(|m| m.method(method)).cloned();
            let mut text = TextBuffer::new(cx);
            match element {
                Some(MethodElement::Hidden(_)) => continue,
                Some(MethodElement::Property(property)) => {
                    if !self.visited.insert(Arc::as_ptr(&property))
                        || !Arc::ptr_eq(&property.class, class)
                    {
                        continue;
                    }
                    property.write(cx, node, &mut text, indent)?;
                    self.separate();
                    self.buffer
                        .append_buffer_for(&text, Some(&class.qualified_name), Some(&key))
                        .append_line_separator();
                }
                Some(MethodElement::Function(function)) => {
                    if !Arc::ptr_eq(&function.class, class) {
                        continue;
                    }
                    function.write(cx, node, &mut text, indent, file)?;
                    self.separate();
                    self.buffer
                        .append_buffer_for(&text, Some(&class.qualified_name), Some(&key));
                }
                Some(MethodElement::Constructor(constructor)) => {
                    if constructor.write_block(cx, node, &mut text, indent)? {
                        self.separate();
                        self.buffer.append_buffer_for(
                            &text,
                            Some(&class.qualified_name),
                            Some(&key),
                        );
                    } else {
                        text.clear_unassigned_bytecode_mapping_data();
                    }
                }
                None => {
                    log::warn!(
                        "Method {} is not associated with Kotlin property or function",
                        method.name
                    );
                    if fallback::write_method(cx, node, index, method, &mut text, indent)? {
                        self.separate();
                        self.buffer.append_buffer(&text);
                    }
                }
            }
        }
        Ok(())
    }
}

fn hidden_method(
    cx: &Cx,
    node: ClassNodeId,
    companion: Option<ClassNodeId>,
    method: &StructMethod,
    key: &str,
) -> bool {
    cx.options.remove_synthetic && method.is_synthetic()
        || cx.options.remove_bridge && method.has_modifier(ACC_BRIDGE)
        || cx.class_nodes[node].hidden_members.contains(key)
        || method.name == INIT_NAME
            && method.descriptor == "(Lkotlin/jvm/internal/DefaultConstructorMarker;)V"
        || method.has_modifier(ACC_STATIC)
            && companion.is_some_and(|id| MethodSlot::by_key(cx, id, key).is_some())
        || method.name.contains("$lambda$")
}
