use std::io;

use super::{invalid, method_slot, modality_of, modality_word, visibility, visibility_of};
use crate::code::code_constants::ACC_INTERFACE;
use crate::decompiler::exps::{Expr, write};
use crate::engine::{Cx, class_nodes::ClassNodeId, class_writer::annotations};
use crate::kotlin::{
    body,
    declarations::KType,
    identifier,
    members::{KProperty, KPropertyAccessor, PropertyInitializer},
    metadata::{
        flags,
        proto::{Modality, Visibility},
    },
    writer::write_method_body,
};
use crate::structs::StructMember;
use crate::util::text_buffer::TextBuffer;

impl KProperty {
    pub fn write(
        &self,
        cx: &mut Cx,
        node: ClassNodeId,
        output: &mut TextBuffer,
        indent: i32,
    ) -> io::Result<()> {
        let mut buffer = TextBuffer::new(cx);
        if flags::HAS_ANNOTATIONS.get(self.flags) {
            for annotation in &self.annotations {
                buffer
                    .append_indent(indent)
                    .append_buffer(&annotations::render(cx, annotation, indent)?)
                    .append_line_separator();
            }
        }
        buffer.append_indent(indent);
        let vis = visibility_of(self.flags)?;
        let modality = modality_of(self.flags)?;
        visibility(cx, &mut buffer, vis);
        if flags::IS_EXPECT_PROPERTY.get(self.flags) {
            buffer.append("expect ");
        }
        if modality == Modality::Final {
            buffer.append(if flags::IS_CONST.get(self.flags) {
                "const "
            } else {
                "final "
            });
        } else if modality != Modality::Abstract || !self.class.has_modifier(ACC_INTERFACE) {
            buffer.append(modality_word(modality));
        }
        if flags::IS_EXTERNAL_PROPERTY.get(self.flags) {
            buffer.append("external ");
        }
        if flags::IS_LATEINIT.get(self.flags) {
            buffer.append("lateinit ");
        }

        let mutable = flags::IS_VAR.get(self.flags);
        buffer
            .append(if mutable { "var " } else { "val " })
            .append(&identifier(&self.name))
            .append(": ");
        let ty = self
            .ty
            .as_ref()
            .ok_or_else(|| invalid("Kotlin property has no type"))?;
        ty.write(cx, &mut buffer, indent)?;
        if let Some(initializer) = self.initializer(cx, node, ty, indent)? {
            if flags::IS_DELEGATED.get(self.flags) {
                buffer.append(" by ").append_buffer(&initializer);
            } else {
                buffer
                    .append(" =")
                    .push_newline_group(indent, 1)
                    .append_possible_newline_or(" ", false)
                    .append_buffer(&initializer)
                    .pop_newline_group();
            }
        }
        if let Some(getter) = &self.getter {
            if flags::IS_NOT_DEFAULT.get(getter.flags) {
                write_accessor(cx, node, &mut buffer, indent, getter, None)?;
            } else if flags::IS_EXTERNAL_ACCESSOR.get(getter.flags) {
                buffer
                    .append_line_separator()
                    .append_indent(indent + 1)
                    .append("external get");
            }
        }
        if let Some(setter) = &self.setter {
            if flags::IS_NOT_DEFAULT.get(setter.flags) {
                let name = self.setter_param_name.as_deref().unwrap_or("null");
                write_accessor(cx, node, &mut buffer, indent, setter, Some(name))?;
            } else {
                let setter_vis = visibility_of(setter.flags)?;
                let setter_modality = modality_of(setter.flags)?;
                let external = flags::IS_EXTERNAL_ACCESSOR.get(setter.flags);
                if external || setter_vis != vis || setter_modality != modality {
                    buffer.append_line_separator().append_indent(indent + 1);
                    if setter_vis != vis {
                        visibility(cx, &mut buffer, setter_vis);
                    }
                    if setter_modality != modality {
                        buffer.append(modality_word(setter_modality));
                    }
                    if external {
                        buffer.append("external ");
                    }
                    buffer.append("set");
                }
            }
        } else if mutable && vis != Visibility::Private {
            buffer
                .append_line_separator()
                .append_indent(indent + 1)
                .append("private set");
        }

        output.append_buffer(&buffer);
        Ok(())
    }

    fn initializer(
        &self,
        cx: &mut Cx,
        node: ClassNodeId,
        property_type: &KType,
        indent: i32,
    ) -> io::Result<Option<TextBuffer>> {
        let Some(initializer) = &self.initializer else {
            return Ok(None);
        };
        match initializer {
            PropertyInitializer::Field { key, is_static } => {
                let wrapper = cx.class_nodes[node]
                    .wrapper
                    .as_ref()
                    .ok_or_else(|| invalid("Kotlin property has no class wrapper"))?;
                let table = if *is_static {
                    &wrapper.static_field_initializers
                } else {
                    &wrapper.dynamic_field_initializers
                };
                let expr = table.get_with_key(key).copied();
                expr.map(|expr| write::to_java(cx, expr, indent))
                    .transpose()
            }
            PropertyInitializer::Constant { ty, value } => {
                let expr =
                    Expr::new_ambient(cx, Expr::constant(ty.clone(), value.clone(), false), None);
                let kotlin = body::replace_expression(cx, expr)?;
                if property_type.unsigned {
                    body::set_unsigned_type(cx, kotlin, property_type.jvm.ty);
                }
                write::to_java(cx, kotlin, indent).map(Some)
            }
        }
    }
}

fn write_accessor(
    cx: &mut Cx,
    node: ClassNodeId,
    buffer: &mut TextBuffer,
    indent: i32,
    accessor: &KPropertyAccessor,
    setter: Option<&str>,
) -> io::Result<()> {
    buffer
        .push_newline_group(indent, 1)
        .append_line_separator()
        .append_indent(indent + 1);
    visibility(cx, buffer, visibility_of(accessor.flags)?);
    buffer.append(modality_word(modality_of(accessor.flags)?));
    if flags::IS_EXTERNAL_ACCESSOR.get(accessor.flags) {
        buffer.append("external ");
    }
    if flags::IS_INLINE_ACCESSOR.get(accessor.flags) {
        buffer.append("inline ");
    }
    if let Some(name) = setter {
        buffer.append("set(").append(name).append(") ");
    } else {
        buffer.append("get() ");
    }
    let slot = method_slot(cx, node, &accessor.method)?;
    write_method_body(cx, node, slot.index(), buffer, indent + 1, false)?;
    buffer.pop_newline_group();
    Ok(())
}
