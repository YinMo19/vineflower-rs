use std::io;

use super::{method_slot, modality_of, modality_word, visibility, visibility_of, write_parameters};
use crate::engine::{Cx, class_nodes::ClassNodeId};
use crate::kotlin::{
    identifier,
    members::KFunction,
    metadata::{flags, proto::Modality},
    writer::{annotations, dump_error, write_code},
};
use crate::structs::attr::TypeAnnotationData;
use crate::types::CodeType;
use crate::util::text_buffer::TextBuffer;

impl KFunction {
    pub fn write(
        &self,
        cx: &mut Cx,
        node: ClassNodeId,
        output: &mut TextBuffer,
        indent: i32,
        is_in_file: bool,
    ) -> io::Result<()> {
        let mut buffer = TextBuffer::new(cx);
        let method = &*self.method;
        annotations::append(
            cx,
            &mut buffer,
            indent,
            method,
            TypeAnnotationData::METHOD_RETURN_TYPE,
        )?;
        annotations::append_jvm(
            &mut buffer,
            indent,
            method,
            false,
            is_in_file,
            &self.class.pool,
            TypeAnnotationData::METHOD_RETURN_TYPE,
        )?;

        buffer.append_indent(indent);
        if !self.context_receiver_types.is_empty() {
            buffer.append("context(");
            for (index, ty) in self.context_receiver_types.iter().enumerate() {
                if index > 0 {
                    buffer.append(", ");
                }
                ty.write(cx, &mut buffer, indent + 1)?;
            }
            buffer
                .append_char(')')
                .append_line_separator()
                .append_indent(indent);
        }
        self.write_modifiers(cx, &mut buffer)?;
        buffer.append("fun ");
        self.write_type_parameters(cx, &mut buffer, indent)?;
        if let Some(receiver) = &self.receiver_type {
            let grouped = !receiver.nullable && receiver.classifier.starts_with("kotlin/Function");
            if grouped {
                buffer.append_char('(');
            }
            receiver.write(cx, &mut buffer, indent + 1)?;
            if grouped {
                buffer.append_char(')');
            }
            buffer.append_char('.');
        }

        buffer
            .append(&identifier(&self.name))
            .append_char('(')
            .push_newline_group(indent, 1)
            .append_possible_newline();
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
        if self.return_type.jvm.ty != CodeType::Void {
            buffer.append(": ");
            self.return_type.write(cx, &mut buffer, indent + 1)?;
        }
        self.write_where_clause(cx, &mut buffer, indent)?;
        buffer.append_char('{').append_line_separator();

        if let Some(contract) = &self.contract {
            contract.write(cx, &mut buffer, indent + 1)?;
        }

        let slot = method_slot(cx, node, method)?;
        let mut code = TextBuffer::new(cx);
        if let Some(nonempty) = write_code(cx, node, slot.index(), &mut code, indent + 1, false)? {
            if nonempty && self.contract.is_some() {
                buffer.append_line_separator();
            }
            buffer.append_buffer(&code);
        }
        if slot.get(cx).decompile_error().is_some() {
            dump_error(cx, node, slot.index(), &mut buffer, indent + 1);
        }
        buffer
            .append_indent(indent)
            .append_char('}')
            .append_line_separator();
        output.append_buffer(&buffer);
        Ok(())
    }

    fn write_modifiers(&self, cx: &Cx, buffer: &mut TextBuffer) -> io::Result<()> {
        visibility(cx, buffer, visibility_of(self.flags)?);
        if flags::IS_EXPECT_FUNCTION.get(self.flags) {
            buffer.append("expect ");
        }
        let modality = modality_of(self.flags)?;
        if modality != Modality::Final && !(self.known_override && modality == Modality::Open) {
            buffer.append(modality_word(modality));
        }
        for (enabled, word) in [
            (flags::IS_EXTERNAL_FUNCTION.get(self.flags), "external "),
            (self.known_override, "override "),
            (flags::IS_TAILREC.get(self.flags), "tailrec "),
            (flags::IS_SUSPEND.get(self.flags), "suspend "),
            (flags::IS_INLINE.get(self.flags), "inline "),
            (flags::IS_INFIX.get(self.flags), "infix "),
            (flags::IS_OPERATOR.get(self.flags), "operator "),
        ] {
            if enabled {
                buffer.append(word);
            }
        }
        Ok(())
    }

    fn write_type_parameters(
        &self,
        cx: &mut Cx,
        buffer: &mut TextBuffer,
        indent: i32,
    ) -> io::Result<()> {
        if self.type_parameters.is_empty() {
            return Ok(());
        }
        buffer.append_char('<');
        for (index, parameter) in self.type_parameters.iter().enumerate() {
            if index > 0 {
                buffer.append(", ");
            }
            if parameter.reified {
                buffer.append("reified ");
            }
            buffer.append(&identifier(&parameter.name));
            if let [bound] = parameter.upper_bounds.as_slice() {
                buffer.append(" : ");
                bound.write(cx, buffer, indent + 1)?;
            }
        }
        buffer.append("> ");
        Ok(())
    }

    fn write_where_clause(
        &self,
        cx: &mut Cx,
        buffer: &mut TextBuffer,
        indent: i32,
    ) -> io::Result<()> {
        let mut bounds = self
            .type_parameters
            .iter()
            .filter(|p| p.upper_bounds.len() > 1)
            .flat_map(|p| p.upper_bounds.iter().map(|bound| (&p.name, bound)))
            .peekable();
        if bounds.peek().is_none() {
            buffer.append_char(' ');
            return Ok(());
        }
        buffer
            .push_newline_group(indent, 1)
            .append_possible_newline_or(" ", false)
            .append("where ");
        for (index, (name, bound)) in bounds.enumerate() {
            if index > 0 {
                buffer
                    .append_possible_newline_or(",", false)
                    .append_possible_newline_or(" ", false);
            }
            buffer.append(&identifier(name)).append(" : ");
            bound.write(cx, buffer, indent + 1)?;
        }
        buffer
            .append_possible_newline_or(" ", true)
            .pop_newline_group();
        Ok(())
    }
}
