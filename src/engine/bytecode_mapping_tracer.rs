// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! `main.collectors.BytecodeMappingTracer`: the source line each bytecode
//! offset of a method ends up on.

use bit_set::BitSet;

use crate::structs::attr::StructLineNumberTableAttribute;
use crate::util::jhash::{JHashMap, JHashSet};

#[derive(Clone, Default)]
pub struct BytecodeMappingTracer {
    current_source_line: i32,
    line_number_table: Option<StructLineNumberTableAttribute>,
    /// bytecode offset, source line
    mapping: JHashMap<i32, i32>,
    unmapped_lines: JHashSet<i32>,
}

impl BytecodeMappingTracer {
    pub fn new(initial_source_line: i32) -> Self {
        Self {
            current_source_line: initial_source_line,
            ..Self::default()
        }
    }

    pub fn increment_current_source_line(&mut self) {
        self.current_source_line += 1;
    }

    /// `incrementCurrentSourceLine(number_lines)`.
    pub fn increment_current_source_line_by(&mut self, number_lines: i32) {
        self.current_source_line += number_lines;
    }

    pub fn add_mapping(&mut self, bytecode_offset: i32) {
        if !self.mapping.contains_key(&bytecode_offset) {
            self.mapping.insert(bytecode_offset, self.current_source_line);
        }
    }

    /// `addMapping(BitSet)`.
    pub fn add_mappings(&mut self, bytecode_offsets: Option<&BitSet>) {
        for offset in bytecode_offsets.into_iter().flatten() {
            self.add_mapping(offset as i32);
        }
    }

    pub fn add_tracer(&mut self, tracer: Option<&BytecodeMappingTracer>) {
        for (&offset, &line) in tracer.iter().flat_map(|tracer| tracer.mapping.iter()) {
            if !self.mapping.contains_key(&offset) {
                self.mapping.insert(offset, line);
            }
        }
    }

    pub fn get_mapping(&self) -> &JHashMap<i32, i32> {
        &self.mapping
    }

    pub fn get_current_source_line(&self) -> i32 {
        self.current_source_line
    }

    pub fn set_current_source_line(&mut self, current_source_line: i32) {
        self.current_source_line = current_source_line;
    }

    pub fn set_line_number_table(&mut self, line_number_table: Option<StructLineNumberTableAttribute>) {
        self.line_number_table = line_number_table;
    }

    pub fn get_unmapped_lines(&self) -> &JHashSet<i32> {
        &self.unmapped_lines
    }

    /// Original line to decompiled line. Also records the original lines
    /// that end up nowhere.
    pub fn get_original_lines_mapping(&mut self) -> JHashMap<i32, i32> {
        let mut res = JHashMap::new();
        let Some(line_number_table) = &self.line_number_table else {
            return res;
        };

        // first match offsets from line number table
        for entry in line_number_table.get_raw_data().chunks_exact(2) {
            let (original_offset, original_line) = (entry[0], entry[1]);
            match self.mapping.get(&original_offset) {
                Some(&new_line) => {
                    res.insert(original_line, new_line);
                }
                None => {
                    self.unmapped_lines.insert(original_line);
                }
            }
        }

        // now match offsets from decompiler mapping
        for (&offset, &line) in self.mapping.iter() {
            let original_line = line_number_table.find_line_number(offset);
            if original_line > -1 && !res.contains_key(&original_line) {
                res.insert(original_line, line);
                self.unmapped_lines.remove(&original_line);
            }
        }

        res
    }
}
