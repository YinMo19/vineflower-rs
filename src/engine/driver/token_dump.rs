// SPDX-License-Identifier: Apache-2.0

//! The optional TextTokenDumpVisitor output.

use crate::engine::Cx;
use crate::util::{text_buffer::TextBuffer, token::TokenKind};

pub(super) fn append(cx: &Cx, buffer: &mut TextBuffer) {
    let mut text = TextBuffer::new(cx);
    text.append_line_separator()
        .append("/*")
        .append_line_separator()
        .append("Tokens:")
        .append_line_separator();
    for token in buffer.get_tokens() {
        let start = buffer.get_pos(token.start);
        let end = buffer.get_pos(token.start + token.length);
        let (kind, value) = match token.kind {
            TokenKind::Class { qualified_name } => ("class", qualified_name),
            TokenKind::Field {
                class_name,
                name,
                descriptor,
            } => (
                "field",
                format!("{class_name}#{name}:{}", descriptor.descriptor_string),
            ),
            TokenKind::Method {
                class_name,
                name,
                descriptor,
            } => ("method", format!("{class_name}#{name}{descriptor}")),
            TokenKind::Variable {
                parameter,
                class_name,
                method_name,
                method_descriptor,
                index,
                name,
            } => {
                let kind = if parameter { "parameter" } else { "local" };
                (
                    kind,
                    format!("{class_name}#{method_name}{method_descriptor}({index}:{name})"),
                )
            }
        };
        let declaration = if token.declaration {
            "declaration"
        } else {
            "reference"
        };
        text.append(&format!("({start}, {end}) {kind} [{declaration}] {value}"))
            .append_line_separator();
    }
    text.append("*/").append_line_separator();
    // The Java visitor appends the text without tokens or mappings.
    buffer.append(&text.convert_to_string_and_allow_data_discard());
}
