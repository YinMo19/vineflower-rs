use std::io;

use super::{invalid, method_content, method_slot, visibility, visibility_of, write_parameters};
use crate::decompiler::{
    exps::{ExprKind, Invocation, literal, write},
    ir::ExprListId,
};
use crate::engine::{
    Cx, class_nodes::ClassNodeId, class_wrapper::MethodSlot, import_collector::get_short_name,
};
use crate::kotlin::{
    members::KConstructor,
    metadata::{
        flags,
        proto::{Visibility, class::Kind},
    },
    writer::annotations,
};
use crate::structs::{StructMethod, attr::TypeAnnotationData};
use crate::util::{interpreter_util::make_unique_key, text_buffer::TextBuffer};

const MARKER: &str = "Lkotlin/jvm/internal/DefaultConstructorMarker;";

impl KConstructor {
    pub fn write_block(
        &self,
        cx: &mut Cx,
        node: ClassNodeId,
        output: &mut TextBuffer,
        indent: i32,
    ) -> io::Result<bool> {
        if self.should_hide(cx)? {
            return Ok(false);
        }
        let method = self.jvm_method()?;
        let slot = method_slot(cx, node, method)?;
        let root = slot
            .get(cx)
            .root()
            .ok_or_else(|| invalid("Kotlin constructor has no method tree"))?;
        let key = make_unique_key(&method.name, &method.descriptor);
        let mut buffer = TextBuffer::new(cx);
        if !self.is_primary {
            if flags::HAS_ANNOTATIONS.get(self.flags) {
                self.write_annotations(cx, &mut buffer, method, indent)?;
            }
            buffer.append_indent(indent);
            visibility(cx, &mut buffer, visibility_of(self.flags)?);
            buffer.append("constructor(").push_newline_group(indent, 1);
            write_parameters(
                cx,
                node,
                method,
                &self.parameters,
                &self.defaults,
                &mut buffer,
                indent,
            )?;

            let expressions = first_expressions(cx, slot)?;
            let Some(&first) = cx.ir[expressions].first() else {
                log::warn!(
                    "Unexpected empty constructor body in {} {}{}",
                    self.class.qualified_name,
                    method.name,
                    method.descriptor
                );
                return Ok(true);
            };
            buffer.append(") ");
            if matches!(cx.ir[first].kind, ExprKind::Invocation(_)) {
                buffer.append(": ");
                buffer.append_buffer_for(
                    &write::to_java(cx, first, indent + 1)?,
                    Some(&self.class.qualified_name),
                    Some(&key),
                );
                cx.ir[expressions].remove(0);
            } else {
                log::warn!(
                    "Unexpected missing super/this constructor call in {} {}{}",
                    self.class.qualified_name,
                    method.name,
                    method.descriptor
                );
            }
        }
        let expressions = first_expressions(cx, slot)?;
        if cx.ir[expressions].is_empty() {
            if self.is_primary {
                return Ok(false);
            }
        } else {
            if self.is_primary {
                buffer.append_indent(indent).append("init");
            }
            buffer.append(" {").append_line_separator();
            buffer.append_buffer_for(
                &method_content(cx, root, indent + 1)?,
                Some(&self.class.qualified_name),
                Some(&key),
            );
            buffer
                .append_indent(indent)
                .append_char('}')
                .append_line_separator();
        }

        output.append_buffer(&buffer);
        Ok(true)
    }

    /// Append the primary signature and consume a super call when it is printed here.
    pub fn write_primary(
        &self,
        cx: &mut Cx,
        node: ClassNodeId,
        output: &mut TextBuffer,
        indent: i32,
    ) -> io::Result<bool> {
        if !self.is_primary {
            return Ok(false);
        }
        let method = self.jvm_method()?;
        let kind = self.class_kind()?;
        let mut buffer = TextBuffer::new(cx);
        if !matches!(kind, Kind::Object | Kind::CompanionObject) {
            let mut explicit = flags::HAS_ANNOTATIONS.get(self.flags);
            if explicit {
                buffer.append_char(' ');
                self.write_annotations(cx, &mut buffer, method, -1)?;
            }
            let vis = visibility_of(self.flags)?;
            if kind != Kind::EnumClass
                && (vis != Visibility::Public || explicit && cx.options.kt_show_public)
            {
                buffer.append_char(' ');
                visibility(cx, &mut buffer, vis);
                explicit = true;
            }
            if explicit {
                buffer.append("constructor");
            }
            if !self.parameters.is_empty() || explicit {
                buffer.append_char('(').push_newline_group(indent, 1);
                write_parameters(
                    cx,
                    node,
                    method,
                    &self.parameters,
                    &self.defaults,
                    &mut buffer,
                    indent,
                )?;
                buffer.append_char(')');
            }
        }

        let slot = method_slot(cx, node, method)?;
        let expressions = first_expressions(cx, slot)?;
        let super_call =
            cx.ir[expressions]
                .first()
                .copied()
                .and_then(|expr| match &cx.ir[expr].kind {
                    ExprKind::Invocation(call) if call.name == "<init>" => {
                        Some((expr, call.classname.clone()))
                    }
                    _ => None,
                });
        let Some((expr, owner)) = super_call else {
            output.append_buffer(&buffer);
            return Ok(false);
        };
        let owner = owner.ok_or_else(|| invalid("Kotlin super constructor has no owner"))?;
        if owner == "java/lang/Object" || kind == Kind::EnumClass {
            output.append_buffer(&buffer);
            return Ok(false);
        }

        let name = get_short_name(cx, &owner.replace('/', "."));
        buffer.append(" : ").append(&name).append_char('(');
        let ExprKind::Invocation(call) = &mut cx.ir[expr].kind else {
            unreachable!()
        };
        remove_marker(call)?;
        buffer
            .append_buffer(&write::append_param_list(cx, expr, indent + 1)?)
            .append_char(')');
        literal::add_offsets(&mut buffer, cx.ir[expr].bytecode.as_ref());
        cx.ir[expressions].remove(0);

        let key = make_unique_key(&method.name, &method.descriptor);
        output.append_buffer_for(&buffer, Some(&self.class.qualified_name), Some(&key));
        Ok(true)
    }

    fn jvm_method(&self) -> io::Result<&StructMethod> {
        self.method
            .as_deref()
            .ok_or_else(|| invalid("Kotlin constructor has no JVM method"))
    }

    fn class_kind(&self) -> io::Result<Kind> {
        flags::CLASS_KIND
            .get(self.class_flags)
            .ok_or_else(|| invalid("Invalid Kotlin class kind"))
    }

    fn should_hide(&self, cx: &Cx) -> io::Result<bool> {
        if !self.is_primary || !self.parameters.is_empty() || !cx.options.hide_default_constructor {
            return Ok(false);
        }
        Ok(
            visibility_of(self.flags)? == visibility_of(self.class_flags)?
                || self.class_kind()? == Kind::EnumClass,
        )
    }

    fn write_annotations(
        &self,
        cx: &mut Cx,
        buffer: &mut TextBuffer,
        method: &StructMethod,
        indent: i32,
    ) -> io::Result<()> {
        let target = TypeAnnotationData::METHOD_RETURN_TYPE;
        annotations::append(cx, buffer, indent, method, target)?;
        annotations::append_jvm(
            buffer,
            indent,
            method,
            false,
            false,
            &self.class.pool,
            target,
        )
    }
}

fn first_expressions(cx: &mut Cx, slot: MethodSlot) -> io::Result<ExprListId> {
    if slot.get(cx).root().is_none() {
        return Err(invalid("Kotlin constructor has no method tree"));
    }
    let graph = cx.wrapper_graph(slot);
    Ok(graph[graph.first].exprents)
}

/// KUtils.removeArguments changes the raw descriptor only for a call with
/// several arguments. The parsed descriptor continues to describe the JVM call.
fn remove_marker(call: &mut Invocation) -> io::Result<()> {
    let marker = crate::types::VarType::from_signature(MARKER);
    match call.parameters.len() {
        0 => return Ok(()),
        1 => {
            if call.descriptor.params.first() == Some(&marker) {
                call.parameters.clear();
            }
            return Ok(());
        }
        _ => {}
    }

    for (index, parameter) in call.descriptor.params.iter().enumerate().rev() {
        if *parameter == marker {
            if index >= call.parameters.len() {
                return Err(invalid("Kotlin constructor marker has no argument"));
            }
            call.parameters.remove(index);
        }
    }
    let descriptor = call.string_descriptor().replace(MARKER, "");
    if descriptor.ends_with(')') {
        return Err(invalid(format!("Invalid descriptor: {descriptor}")));
    }
    call.descriptor_text = Some(descriptor.into());
    Ok(())
}
