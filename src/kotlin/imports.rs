//! The additional reserved names and implicit packages of KotlinImportCollector.

use super::types::MAPPED_CLASSES;
use crate::engine::{Cx, import_collector::ImportCollector};
use crate::util::text_buffer::TextBuffer;

/// A Kotlin writer starts with all resolutions made while processing its class.
pub fn from_parent(parent: &ImportCollector) -> ImportCollector {
    let mut collector = parent.clone();
    for &name in MAPPED_CLASSES {
        let (package, simple) = name
            .rsplit_once('/')
            .expect("Expected a mapped Kotlin class");
        collector.reserve_name(simple, &package.replace('/', "."));
    }
    collector
}

/// Write import statements for a Kotlin compilation unit.
pub fn write_imports(cx: &Cx, buffer: &mut TextBuffer, separator: bool) {
    if cx.options.remove_imports {
        return;
    }
    let collector = from_parent(&cx.imports);
    let imports = collector.imports_matching(|package| {
        !matches!(
            package,
            "kotlin"
                | "kotlin.annotation"
                | "kotlin.collections"
                | "kotlin.comparisons"
                | "kotlin.io"
                | "kotlin.jvm"
                | "kotlin.ranges"
                | "kotlin.sequences"
                | "kotlin.text"
        )
    });
    for name in &imports {
        buffer
            .append("import ")
            .append(name)
            .append_line_separator();
    }
    if separator && !imports.is_empty() {
        buffer.append_line_separator();
    }
}
