//! Per-compilation-unit aggregation of method bytecode and original source lines.

use super::bytecode_mapping_tracer::BytecodeMappingTracer;
use crate::util::{jhash::JHashMap, text_buffer::TextBuffer};
use indexmap::IndexMap;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Default)]
pub struct BytecodeSourceMapper {
    offset_total: i32,
    // Classes and methods follow first use. Offsets are sorted for the dump.
    mappings: IndexMap<String, IndexMap<String, BTreeMap<i32, i32>>>,
    original_lines: JHashMap<i32, i32>,
    unmapped_lines: BTreeSet<i32>,
}

impl BytecodeSourceMapper {
    pub fn add_tracer(&mut self, class: &str, method: &str, tracer: &mut BytecodeMappingTracer) {
        if !tracer.get_mapping().is_empty() {
            let offsets = self
                .mappings
                .entry(class.to_owned())
                .or_default()
                .entry(method.to_owned())
                .or_default();
            for (&offset, &line) in tracer.get_mapping().iter() {
                offsets.entry(offset).or_insert(line);
            }
        }
        let lines = tracer.get_original_lines_mapping();
        self.original_lines
            .put_all(lines.iter().map(|(&from, &to)| (from, to)), lines.len());
        self.unmapped_lines
            .extend(tracer.get_unmapped_lines().iter().copied());
    }

    pub fn add_total_offset(&mut self, lines: i32) {
        self.offset_total += lines;
    }

    pub fn original_lines_mapping(&mut self) -> Vec<i32> {
        let mut pairs = Vec::with_capacity(2 * self.original_lines.len());
        for (&old, &new) in self.original_lines.iter() {
            self.unmapped_lines.remove(&old);
            pairs.extend([old, new + self.offset_total + 1]);
        }
        pairs
    }

    pub fn dump_mapping(&self, buf: &mut TextBuffer, hex: bool) {
        if self.mappings.is_empty() && self.original_lines.is_empty() {
            return;
        }
        for (class, methods) in &self.mappings {
            buf.append("class '")
                .append(class)
                .append("' {")
                .append_line_separator();
            for (i, (method, offsets)) in methods.iter().enumerate() {
                if i != 0 {
                    buf.append_line_separator();
                }
                buf.append_indent(1)
                    .append("method '")
                    .append(method)
                    .append("' {")
                    .append_line_separator();
                for (&offset, &line) in offsets {
                    let offset = if hex {
                        format!("{offset:x}")
                    } else {
                        line.to_string()
                    };
                    buf.append_indent(2)
                        .append(&offset)
                        .append_indent(2)
                        .append(&(line + self.offset_total).to_string())
                        .append_line_separator();
                }
                buf.append_indent(1)
                    .append_char('}')
                    .append_line_separator();
            }
            buf.append_char('}')
                .append_line_separator()
                .append_line_separator();
        }
        buf.append("Lines mapping:").append_line_separator();
        let sorted: BTreeMap<_, _> = self.original_lines.iter().collect();
        for (old, new) in sorted {
            buf.append(&old.to_string())
                .append(" <-> ")
                .append(&(new + self.offset_total + 1).to_string())
                .append_line_separator();
        }
        if !self.unmapped_lines.is_empty() {
            buf.append("Not mapped:").append_line_separator();
            for line in &self.unmapped_lines {
                if !self.original_lines.contains_key(line) {
                    buf.append(&line.to_string()).append_line_separator();
                }
            }
        }
    }
}
