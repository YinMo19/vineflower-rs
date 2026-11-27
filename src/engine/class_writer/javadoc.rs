//! Optional source documentation supplied by an embedder (IFabricJavadocProvider).

use crate::structs::{StructClass, StructField, StructMethod};
use crate::util::text_buffer::TextBuffer;

#[derive(Clone, Copy, Default)]
pub enum JavadocStyle {
    #[default]
    Html,
    Markdown,
}

pub trait JavadocProvider: Send + Sync {
    fn class_doc(&self, _class: &StructClass) -> Option<String> {
        None
    }
    fn field_doc(&self, _class: &StructClass, _field: &StructField) -> Option<String> {
        None
    }
    fn method_doc(&self, _class: &StructClass, _method: &StructMethod) -> Option<String> {
        None
    }
    fn class_style(&self, _class: &StructClass) -> JavadocStyle {
        JavadocStyle::Html
    }
    fn field_style(&self, class: &StructClass, _field: &StructField) -> JavadocStyle {
        self.class_style(class)
    }
    fn method_style(&self, class: &StructClass, _method: &StructMethod) -> JavadocStyle {
        self.class_style(class)
    }
}

pub(crate) fn append(buffer: &mut TextBuffer, style: JavadocStyle, text: &str, indent: i32) {
    let (prefix, delimited) = match style {
        JavadocStyle::Html => (" * ", true),
        JavadocStyle::Markdown => ("/// ", false),
    };
    if delimited {
        buffer
            .append_indent(indent)
            .append("/**")
            .append_line_separator();
    }
    // String.split("\\n") drops all trailing empty strings except for empty input.
    let trimmed = text.trim_end_matches('\n');
    if !trimmed.is_empty() || text.is_empty() {
        for line in trimmed.split('\n') {
            buffer
                .append_indent(indent)
                .append(prefix)
                .append(line)
                .append_line_separator();
        }
    }
    if delimited {
        buffer
            .append_indent(indent)
            .append(" */")
            .append_line_separator();
    }
}
