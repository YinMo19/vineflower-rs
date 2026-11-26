// SPDX-License-Identifier: Apache-2.0

//! Annotation values, use-site prefixes and modifiers represented by JVM annotations.

use std::io;

use rustc_hash::FxHashSet;

use crate::{
    code::code_constants::*,
    decompiler::exps::literal,
    engine::{
        Cx,
        class_writer::{annotations as java, type_annotations},
        import_collector::get_short_name,
    },
    kotlin::types::kotlin_type,
    structs::{
        StructMember,
        attr::{AnnotationData, ElementValue, TypeAnnotationData},
        consts::ConstantPool,
        struct_member::Attributes,
    },
    types::VarType,
    util::text_buffer::TextBuffer,
};

const NOT_NULL: &str = "org/jetbrains/annotations/NotNull";
const NULLABLE: &str = "org/jetbrains/annotations/Nullable";

#[derive(Clone, Copy, Debug)]
pub enum UseSiteTarget {
    File,
    Property,
    Field,
    Get,
    Set,
    Receiver,
    Param,
    SetParam,
    Delegate,
}

impl UseSiteTarget {
    fn spelling(self) -> &'static str {
        match self {
            Self::File => "file",
            Self::Property => "property",
            Self::Field => "field",
            Self::Get => "get",
            Self::Set => "set",
            Self::Receiver => "receiver",
            Self::Param => "param",
            Self::SetParam => "setparam",
            Self::Delegate => "delegate",
        }
    }
}

pub fn render(
    cx: &mut Cx,
    annotation: &AnnotationData,
    indent: i32,
    target: Option<UseSiteTarget>,
) -> io::Result<TextBuffer> {
    // KAnnotationExprent creates new wrappers for its direct values. A KNewExprent
    // shares its element list, while a nested KAnnotationExprent wraps its values.
    allocate_wrapper(cx, annotation);
    render_wrapped(cx, annotation, indent, target)
}

fn render_wrapped(
    cx: &mut Cx,
    annotation: &AnnotationData,
    indent: i32,
    target: Option<UseSiteTarget>,
) -> io::Result<TextBuffer> {
    let mut buffer = TextBuffer::new(cx);
    buffer.append_indent(indent).append_char('@');
    if let Some(site) = target {
        buffer.append(site.spelling()).append_char(':');
    }
    write_annotation(cx, &mut buffer, annotation, true)?;
    Ok(buffer)
}

fn allocate_wrapper(cx: &Cx, annotation: &AnnotationData) {
    for value in &annotation.par_values {
        if let ElementValue::Annotation(nested) = &value.value {
            allocate_wrapper(cx, nested);
        } else {
            cx.expression_ids.next();
        }
    }
    cx.expression_ids.next();
}

fn write_annotation(
    cx: &mut Cx,
    buffer: &mut TextBuffer,
    annotation: &AnnotationData,
    wrap: bool,
) -> io::Result<()> {
    let ty = VarType::from_signature_cl(&annotation.class_name, true);
    buffer.append(&kotlin_type(cx, Some(&ty), true)?);
    if annotation.par_names.is_empty() {
        return Ok(());
    }
    let single = annotation.par_names.as_slice() == ["value"];
    buffer.append_char('(');
    if wrap {
        buffer.append_possible_newline();
    }
    for (index, (name, value)) in annotation
        .par_names
        .iter()
        .zip(&annotation.par_values)
        .enumerate()
    {
        if index > 0 {
            buffer.append_char(',');
            if wrap {
                buffer.append_possible_newline_or(" ", false);
            } else {
                buffer.append_char(' ');
            }
        }
        if !single {
            buffer.append(name).append(" = ");
        }
        write_value(cx, buffer, &value.value)?;
    }
    buffer.append_char(')');
    Ok(())
}

pub fn write_value(cx: &mut Cx, buffer: &mut TextBuffer, value: &ElementValue) -> io::Result<()> {
    match value {
        ElementValue::Array(elements) => {
            buffer.append_char('[');
            for (index, element) in elements.iter().enumerate() {
                if index > 0 {
                    buffer.append(", ");
                }
                write_value(cx, buffer, &element.value)?;
            }
            buffer.append_char(']');
        }
        ElementValue::Annotation(annotation) => {
            buffer.append_char('@');
            write_annotation(cx, buffer, annotation, false)?;
        }
        ElementValue::Class(name) => {
            get_short_name(cx, name);
            let ty = VarType::from_signature_cl(name, true);
            buffer
                .append(&kotlin_type(cx, Some(&ty), true)?)
                .append("::class");
        }
        ElementValue::EnumConstant {
            const_name,
            descriptor,
        } => {
            let owner = descriptor.ty.name();
            get_short_name(cx, owner);
            let ty = VarType::from_signature_cl(owner, true);
            buffer
                .append(&kotlin_type(cx, Some(&ty), true)?)
                .append_char('.')
                .append(const_name);
        }
        ElementValue::Const { ty, value } => {
            buffer.append_buffer(&literal::render(cx, ty, value, None, false)?);
        }
    }
    Ok(())
}

/// Kotlin's default-argument map wraps an annotation value when the map is built.
#[derive(Clone, Debug)]
pub struct DefaultValue(ElementValue);

impl DefaultValue {
    pub fn from_element(cx: &Cx, value: &ElementValue) -> Self {
        if let ElementValue::Annotation(annotation) = value {
            allocate_wrapper(cx, annotation);
        } else {
            cx.expression_ids.next();
        }
        Self(value.clone())
    }

    pub fn render(&self, cx: &mut Cx, indent: i32) -> io::Result<TextBuffer> {
        match &self.0 {
            ElementValue::Class(name) => {
                let mut buffer = TextBuffer::new(cx);
                crate::kotlin::body::append_class_literal(cx, &mut buffer, name);
                Ok(buffer)
            }
            ElementValue::Annotation(annotation) => render_wrapped(cx, annotation, indent, None),
            ElementValue::Array(elements) => {
                let mut buffer = TextBuffer::new(cx);
                buffer
                    .append_char('[')
                    .push_newline_group(indent, 1)
                    .append_possible_newline();
                for (index, element) in elements.iter().enumerate() {
                    if index > 0 {
                        buffer
                            .append_char(',')
                            .append_possible_newline_or(" ", false);
                    }
                    buffer.append_buffer(&java::render_element(cx, &element.value, indent)?);
                }
                buffer
                    .append_possible_newline_or("", true)
                    .pop_newline_group()
                    .append_char(']');
                Ok(buffer)
            }
            value => java::render_element(cx, value, indent),
        }
    }
}

pub fn render_element(cx: &mut Cx, value: &ElementValue, indent: i32) -> io::Result<TextBuffer> {
    DefaultValue::from_element(cx, value).render(cx, indent)
}

pub fn append(
    cx: &mut Cx,
    buf: &mut TextBuffer,
    indent: i32,
    member: &impl StructMember,
    target: i32,
) -> io::Result<()> {
    append_except(cx, buf, indent, member, target, |_| false)
}

pub(super) fn append_except(
    cx: &mut Cx,
    buf: &mut TextBuffer,
    indent: i32,
    member: &impl StructMember,
    target: i32,
    mut removed: impl FnMut(&AnnotationData) -> bool,
) -> io::Result<()> {
    let attrs = member.attributes();
    let mut filter = FxHashSet::default();
    for annotation in java::declaration_annotations(attrs).filter(|a| {
        !removed(a)
            && !matches!(
                a.class_name.as_str(),
                "kotlin/Metadata" | NOT_NULL | NULLABLE | "kotlin/jvm/JvmStatic"
            )
    }) {
        let text = render(cx, annotation, indent, None)?.convert_to_string_and_allow_data_discard();
        buf.append(&text);
        finish(buf, indent);
        filter.insert(text);
    }
    append_type_annotations(cx, buf, indent, attrs, target, -1, &filter)
}

fn finish(buf: &mut TextBuffer, indent: i32) {
    if indent < 0 {
        buf.append_char(' ');
    } else {
        buf.append_line_separator();
    }
}

fn append_type_annotations(
    cx: &mut Cx,
    buf: &mut TextBuffer,
    indent: i32,
    attrs: &Attributes,
    target: i32,
    index: i32,
    filter: &FxHashSet<String>,
) -> io::Result<()> {
    for entry in
        type_annotations::for_target(attrs, target, index).filter(|entry| entry.is_top_level())
    {
        let text =
            java::render(cx, &entry.annotation, indent)?.convert_to_string_and_allow_data_discard();
        if !filter.contains(&text) {
            buf.append(&text);
            finish(buf, indent);
        }
    }
    Ok(())
}

pub fn parameter(
    cx: &mut Cx,
    buf: &mut TextBuffer,
    attrs: &Attributes,
    index: usize,
) -> io::Result<bool> {
    let mut filter = FxHashSet::default();
    let mut nullable = false;
    for annotation in java::parameter_annotations(attrs, index) {
        match annotation.class_name.as_str() {
            NOT_NULL => {}
            NULLABLE => nullable = true,
            _ => {
                let text =
                    java::render(cx, annotation, -1)?.convert_to_string_and_allow_data_discard();
                buf.append(&text).append_char(' ');
                filter.insert(text);
            }
        }
    }
    append_type_annotations(
        cx,
        buf,
        -1,
        attrs,
        TypeAnnotationData::METHOD_PARAMETER,
        index as i32,
        &filter,
    )?;
    Ok(nullable)
}

/// KotlinWriter.isNullable inspects the first available declaration-annotation attribute.
pub fn is_nullable(member: &impl StructMember) -> bool {
    let attrs = member.attributes();
    attrs
        .runtime_visible_annotations
        .as_ref()
        .or(attrs.runtime_invisible_annotations.as_ref())
        .is_some_and(|attr| attr.annotations.iter().any(|a| a.class_name == NULLABLE))
}

pub fn append_jvm(
    buf: &mut TextBuffer,
    indent: i32,
    member: &impl StructMember,
    is_interface: bool,
    is_in_file: bool,
    pool: &ConstantPool,
    target: i32,
) -> io::Result<()> {
    let line = |buf: &mut TextBuffer, name: &str| {
        buf.append_indent(indent)
            .append(name)
            .append_line_separator();
    };
    match target {
        TypeAnnotationData::METHOD_RETURN_TYPE => {
            if is_interface && !member.has_modifier(ACC_ABSTRACT) {
                line(buf, "@JvmDefault");
            }
            if member.has_modifier(ACC_SYNCHRONIZED) {
                line(buf, "@Synchronized");
            }
            if let Some(attr) = &member.attributes().exceptions {
                buf.append_indent(indent)
                    .append("@Throws(")
                    .push_newline_group(indent, 1);
                for (index, constant) in attr.throws_exceptions.iter().enumerate() {
                    if index > 0 {
                        buf.append_char(',').append_possible_newline_or(" ", false);
                    }
                    let class = pool.get_primitive_constant(*constant).ok_or_else(|| {
                        io::Error::other("Missing exception type in the constant pool")
                    })?;
                    buf.append(class.get_string()).append("::class");
                }
                buf.pop_newline_group()
                    .append_char(')')
                    .append_line_separator();
            }
        }
        TypeAnnotationData::FIELD => {
            if member.has_modifier(ACC_TRANSIENT) {
                line(buf, "@Transient");
            }
            if member.has_modifier(ACC_VOLATILE) {
                line(buf, "@Volatile");
            }
        }
        TypeAnnotationData::CLASS_TYPE_PARAMETER if member.attributes().record.is_some() => {
            line(buf, "@JvmRecord")
        }
        _ => {}
    }
    if member.has_modifier(ACC_STATIC)
        && target != TypeAnnotationData::CLASS_TYPE_PARAMETER
        && !is_in_file
        && !member.has_modifier(ACC_ENUM)
    {
        line(buf, "@JvmStatic");
    }
    if member.has_modifier(ACC_STRICT) {
        line(buf, "@Strictfp");
    }
    if member.has_modifier(ACC_SYNTHETIC) {
        line(buf, "@JvmSynthetic");
    }
    Ok(())
}
