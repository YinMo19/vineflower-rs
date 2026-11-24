// Based on Vineflower BytecodeMappingTracer and BytecodeSourceMapper.
// Copyright 2000-2018 JetBrains s.r.o. (Apache-2.0).
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::Write,
};

/// Mapping from original bytecode and debug lines to emitted source lines.
#[derive(Debug, Default)]
pub struct SourceMap {
    /// Methods in class-file order. Source lines are zero-based.
    pub methods: Vec<MethodMap>,
    /// Original and decompiled source lines, both one-based.
    pub original_lines: BTreeMap<u16, usize>,
    pub unmapped_lines: BTreeSet<u16>,
}

#[derive(Debug)]
pub struct MethodMap {
    pub name: String,
    pub descriptor: String,
    pub offsets: BTreeMap<u32, usize>,
}

impl SourceMap {
    pub(super) fn add(&mut self, map: MethodMap, mut lines: Vec<(u16, u16)>) {
        lines.sort_by_key(|&(offset, _)| offset);
        let mut mapped = BTreeMap::new();
        let mut unmapped = BTreeSet::new();
        for &(offset, original) in &lines {
            if let Some(&source) = map.offsets.get(&u32::from(offset)) {
                mapped.insert(original, source + 1);
            } else {
                unmapped.insert(original);
            }
        }
        for (&offset, &source) in &map.offsets {
            let i = lines.partition_point(|&(start, _)| u32::from(start) <= offset);
            if i != 0 {
                let original = lines[i - 1].1;
                mapped.entry(original).or_insert(source + 1);
                unmapped.remove(&original);
            }
        }
        self.original_lines.extend(mapped);
        self.unmapped_lines.extend(unmapped);
        if !map.offsets.is_empty() {
            self.methods.push(map);
        }
    }

    pub(super) fn shift(&mut self, lines: usize) {
        for method in &mut self.methods {
            for source in method.offsets.values_mut() {
                *source += lines;
            }
        }
        for source in self.original_lines.values_mut() {
            *source += lines;
        }
    }

    pub(super) fn annotate(&self, source: &str, output: &mut String) {
        let mut by_source: BTreeMap<usize, Vec<u16>> = BTreeMap::new();
        for (&original, &source) in &self.original_lines {
            by_source.entry(source).or_default().push(original);
        }
        for (index, line) in source.split_inclusive('\n').enumerate() {
            match (by_source.get(&(index + 1)), line.strip_suffix('\n')) {
                (Some(originals), Some(line)) => {
                    output.push_str(line);
                    output.push_str("//");
                    for original in originals {
                        let _ = write!(output, " {original}");
                    }
                    output.push('\n');
                }
                _ => output.push_str(line),
            }
        }
    }

    pub(super) fn dump(&self, class: &str, indent: &str, output: &mut String) {
        if self.methods.is_empty() && self.original_lines.is_empty() {
            return;
        }
        let _ = writeln!(output, "\nclass '{class}' {{");
        for (index, method) in self.methods.iter().enumerate() {
            if index != 0 {
                output.push('\n');
            }
            let _ = writeln!(
                output,
                "{indent}method '{} {}' {{",
                method.name, method.descriptor
            );
            for (&offset, &line) in &method.offsets {
                let _ = writeln!(output, "{indent}{indent}{offset:x}{indent}{indent}{line}");
            }
            let _ = writeln!(output, "{indent}}}");
        }
        output.push_str("}\n\nLines mapping:\n");
        for (original, source) in &self.original_lines {
            let _ = writeln!(output, "{original} <-> {source}");
        }
        if !self.unmapped_lines.is_empty() {
            output.push_str("Not mapped:\n");
            for original in &self.unmapped_lines {
                if !self.original_lines.contains_key(original) {
                    let _ = writeln!(output, "{original}");
                }
            }
        }
    }
}
