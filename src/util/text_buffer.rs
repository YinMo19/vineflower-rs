// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! `util.TextBuffer`: generated source text together with the bytecode
//! offsets, tokens and optional line breaks attached to positions in it.
//!
//! The text is kept in UTF-16 so that every position, length and line width
//! is the number upstream computes on its `StringBuilder`.
//!
//! Left out: the line-to-offset map, which nothing in upstream can fill and
//! which therefore never changes the output, and the `DebugTrace` leak
//! detector of unit-test mode.

use std::collections::BTreeSet;
use std::sync::Arc;

use bit_set::BitSet;
use indexmap::IndexMap;
use rustc_hash::FxHashMap;

use super::java_str::utf16_len;
use super::token::{TextToken, TextTokenVisitor, TokenKind};
use crate::engine::bytecode_mapping_tracer::BytecodeMappingTracer;
use crate::engine::{Cx, Options};
use crate::types::{FieldDescriptor, MethodDescriptor};

#[derive(Clone)]
pub struct TextBuffer {
    options: Arc<Options>,
    text: Vec<u16>,
    root_group: NewlineGroup,
    /// The child indices leading from the root group to the current one.
    current_group: Vec<usize>,
    has_reformatted: bool,
    /// Bytecode offset to offset in the text, in insertion order.
    bytecode_offset_mapping: IndexMap<BytecodeMappingKey, i32>,
    /// New line number to original line numbers.
    line_mapping: Option<FxHashMap<i32, BTreeSet<i32>>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct BytecodeMappingKey {
    bytecode_offset: i32,
    /// `None` signifies the current class.
    class: Option<String>,
    method: Option<String>,
}

impl BytecodeMappingKey {
    fn unassigned(bytecode_offset: i32) -> Self {
        Self {
            bytecode_offset,
            class: None,
            method: None,
        }
    }
}

#[derive(Clone, Default)]
struct NewlineGroup {
    start: i32,
    length: i32,
    base_indent: i32,
    extra_indent: i32,
    children: Vec<NewlineGroup>,
    replacements: Vec<Replacement>,
    tokens: Vec<TextToken>,
}

#[derive(Clone, Copy)]
struct Replacement {
    start: i32,
    length: i32,
    dedent: bool,
}

impl NewlineGroup {
    fn new(start: i32, base_indent: i32, extra_indent: i32) -> Self {
        Self {
            start,
            base_indent,
            extra_indent,
            ..Self::default()
        }
    }

    fn shift(&mut self, amount: i32) {
        self.start += amount;
        for replacement in &mut self.replacements {
            replacement.start += amount;
        }
        for token in &mut self.tokens {
            token.shift(amount);
        }
        for child in &mut self.children {
            child.shift(amount);
        }
    }

    fn truncate(&mut self, string_length: i32) {
        if self.start + self.length > string_length {
            self.length = string_length - self.start;
        }
        self.children.retain_mut(|child| {
            let kept = child.start <= string_length;
            if kept {
                child.truncate(string_length);
            }
            kept
        });
        self.replacements
            .retain(|replacement| replacement.start <= string_length);
        self.tokens.retain(|token| token.start <= string_length);
    }

    fn flatten_tokens(&self) -> Vec<TextToken> {
        let mut result = self.tokens.clone();
        for child in &self.children {
            result.extend(child.flatten_tokens());
        }
        result.sort_by_key(|token| token.start);
        result
    }
}

impl TextBuffer {
    pub fn new(cx: &Cx) -> Self {
        Self::with_capacity(cx, 0)
    }

    /// `new TextBuffer(size)`.
    pub fn with_capacity(cx: &Cx, size: usize) -> Self {
        Self {
            options: Arc::clone(&cx.options),
            text: Vec::with_capacity(size),
            root_group: NewlineGroup::default(),
            current_group: Vec::new(),
            has_reformatted: false,
            bytecode_offset_mapping: IndexMap::new(),
            line_mapping: None,
        }
    }

    /// `new TextBuffer(text)`.
    pub fn from_text(cx: &Cx, text: &str) -> Self {
        let mut buffer = Self::new(cx);
        buffer.append(text);
        buffer
    }

    pub fn append(&mut self, text: &str) -> &mut Self {
        self.text.extend(text.encode_utf16());
        self
    }

    /// `append(char)`.
    pub fn append_char(&mut self, ch: char) -> &mut Self {
        self.text.extend(ch.encode_utf16(&mut [0; 2]).iter());
        self
    }

    /// `append(int)`.
    pub fn append_int(&mut self, value: i32) -> &mut Self {
        self.append(&value.to_string())
    }

    pub fn append_line_separator(&mut self) -> &mut Self {
        let separator = self.options.line_separator();
        self.append(separator)
    }

    pub fn append_indent(&mut self, length: i32) -> &mut Self {
        let options = Arc::clone(&self.options);
        for _ in 0..length {
            self.append(&options.indent_string);
        }
        self
    }

    pub fn append_all_classes(&mut self, text: &str, qualified_name: &str) -> &mut Self {
        self.add_all_class_tokens(self.length(), text, qualified_name);
        self.append(text)
    }

    /// Tokens for each class of a possibly nested, possibly generic type name
    /// such as `Outer.Inner<T>` that starts at `index`.
    pub fn add_all_class_tokens(
        &mut self,
        mut index: i32,
        text: &str,
        qualified_name: &str,
    ) -> &mut Self {
        let mut text = text.find('<').map_or(text, |generics| &text[..generics]);

        let mut pos = 0;
        while let (Some(dot), Some(dollar)) = (text.find('.'), qualified_name[pos..].find('$')) {
            let length = utf16_len(&text[..dot]);
            self.add_class_token(index, length, &qualified_name[..pos + dollar]);
            pos += dollar + 1;
            text = &text[dot + 1..];
            index += length + 1;
        }

        if !text.trim().is_empty() {
            self.add_class_token(index, utf16_len(text), qualified_name);
        }

        self
    }

    pub fn add_class_token(&mut self, index: i32, length: i32, name: &str) -> &mut Self {
        self.add_token(TextToken::new(
            index,
            length,
            false,
            TokenKind::Class {
                qualified_name: name.to_owned(),
            },
        ));
        self
    }

    pub fn append_class(
        &mut self,
        value: &str,
        declaration: bool,
        qualified_name: &str,
    ) -> &mut Self {
        self.add_token(TextToken::new(
            self.length(),
            utf16_len(value),
            declaration,
            TokenKind::Class {
                qualified_name: qualified_name.to_owned(),
            },
        ));
        self.append(value)
    }

    /// `appendField(value, declaration, className, name, String descriptor)`.
    pub fn append_field(
        &mut self,
        value: &str,
        declaration: bool,
        class_name: &str,
        name: &str,
        descriptor: &str,
    ) -> &mut Self {
        self.append_field_with(
            value,
            declaration,
            class_name,
            name,
            FieldDescriptor::parse_descriptor(descriptor),
        )
    }

    /// `appendField(value, declaration, className, name, FieldDescriptor descriptor)`.
    pub fn append_field_with(
        &mut self,
        value: &str,
        declaration: bool,
        class_name: &str,
        name: &str,
        descriptor: FieldDescriptor,
    ) -> &mut Self {
        self.add_token(TextToken::new(
            self.length(),
            utf16_len(value),
            declaration,
            TokenKind::Field {
                class_name: class_name.to_owned(),
                name: name.to_owned(),
                descriptor,
            },
        ));
        self.append(value)
    }

    /// `appendMethod(value, declaration, className, name, String descriptor)`.
    pub fn append_method(
        &mut self,
        value: &str,
        declaration: bool,
        class_name: &str,
        name: &str,
        descriptor: &str,
    ) -> &mut Self {
        self.append_method_with(
            value,
            declaration,
            class_name,
            name,
            MethodDescriptor::parse_descriptor(descriptor),
        )
    }

    /// `appendMethod(value, declaration, className, name, MethodDescriptor descriptor)`.
    pub fn append_method_with(
        &mut self,
        value: &str,
        declaration: bool,
        class_name: &str,
        name: &str,
        descriptor: MethodDescriptor,
    ) -> &mut Self {
        self.add_token(TextToken::new(
            self.length(),
            utf16_len(value),
            declaration,
            TokenKind::Method {
                class_name: class_name.to_owned(),
                name: name.to_owned(),
                descriptor,
            },
        ));
        self.append(value)
    }

    /// `appendVariable` with the method descriptor already parsed.
    #[allow(clippy::too_many_arguments)]
    pub fn append_variable(
        &mut self,
        value: &str,
        declaration: bool,
        parameter: bool,
        class_name: &str,
        method_name: &str,
        method_descriptor: MethodDescriptor,
        index: i32,
        name: &str,
    ) -> &mut Self {
        self.add_token(TextToken::new(
            self.length(),
            utf16_len(value),
            declaration,
            TokenKind::Variable {
                parameter,
                class_name: class_name.to_owned(),
                method_name: method_name.to_owned(),
                method_descriptor,
                index,
                name: name.to_owned(),
            },
        ));
        self.append(value)
    }

    pub(super) fn add_token(&mut self, token: TextToken) {
        self.current_group_mut().tokens.push(token);
    }

    fn current_group_mut(&mut self) -> &mut NewlineGroup {
        self.current_group
            .iter()
            .fold(&mut self.root_group, |group, &child| {
                &mut group.children[child]
            })
    }

    /// Pushes a newline group.
    ///
    /// [`append_possible_newline`](Self::append_possible_newline) normally
    /// works like `append`, adding its string argument to the buffer. However,
    /// if the line is running out of space, this text may later be replaced
    /// with a newline (plus indents). Possible newlines are grouped into
    /// newline groups. In a newline group, either none of the replacements are
    /// replaced with newlines, or all of them are (never only some of them).
    /// Possible newlines should not be added outside a group. The API works as
    /// if there were a stack of newline groups. This method pushes to the
    /// stack and [`pop_newline_group`](Self::pop_newline_group) pops from it.
    /// After the full source code has been generated,
    /// [`reformat`](Self::reformat) is called to actually substitute the text.
    ///
    /// `base_indent` is the indent that has already been explicitly applied,
    /// `extra_indent` the indent to be added if this group is applied.
    pub fn push_newline_group(&mut self, base_indent: i32, extra_indent: i32) -> &mut Self {
        let group = NewlineGroup::new(self.length(), base_indent, extra_indent);
        let current = self.current_group_mut();
        current.children.push(group);
        let child = current.children.len() - 1;
        self.current_group.push(child);
        self
    }

    /// If the current group is applied, add a newline here.
    pub fn append_possible_newline(&mut self) -> &mut Self {
        self.append_possible_newline_or("", false)
    }

    /// If the current group is applied, add a newline here. Otherwise, add
    /// `alternative`. If `dedent` is true, the extra indent from this group is
    /// unapplied from this point on.
    pub fn append_possible_newline_or(&mut self, alternative: &str, dedent: bool) -> &mut Self {
        let replacement = Replacement {
            start: self.length(),
            length: utf16_len(alternative),
            dedent,
        };
        self.current_group_mut().replacements.push(replacement);
        self.append(alternative)
    }

    pub fn pop_newline_group(&mut self) -> &mut Self {
        if self.current_group.is_empty() {
            panic!(
                "Cannot pop root group: {}",
                self.convert_to_string_and_allow_data_discard()
            );
        }
        let length = self.length();
        let current = self.current_group_mut();
        current.length = length - current.start;
        self.current_group.pop();
        self
    }

    pub fn prepend(&mut self, text: &str) -> &mut Self {
        self.text.splice(0..0, text.encode_utf16());
        self.shift_mapping(utf16_len(text));
        self
    }

    pub fn enclose(&mut self, left: &str, right: &str) -> &mut Self {
        self.prepend(left);
        self.append(right)
    }

    pub fn enclose_with_parens(&mut self) -> &mut Self {
        self.enclose("(", ")")
    }

    pub fn contains_only_whitespaces(&self) -> bool {
        self.text.iter().all(|&unit| unit == u16::from(b' '))
    }

    pub fn add_bytecode_mapping(&mut self, bytecode_offset: i32) {
        let length = self.length();
        self.bytecode_offset_mapping
            .entry(BytecodeMappingKey::unassigned(bytecode_offset))
            .or_insert(length);
    }

    pub fn add_start_bytecode_mapping(&mut self, bytecode_offset: i32) {
        self.bytecode_offset_mapping
            .entry(BytecodeMappingKey::unassigned(bytecode_offset))
            .or_insert(0);
    }

    /// `addBytecodeMapping(BitSet)`.
    pub fn add_bytecode_mappings(&mut self, bytecode_offsets: Option<&BitSet>) {
        for offset in bytecode_offsets.into_iter().flatten() {
            self.add_bytecode_mapping(offset as i32);
        }
    }

    /// `addStartBytecodeMapping(BitSet)`.
    pub fn add_start_bytecode_mappings(&mut self, bytecode_offsets: Option<&BitSet>) {
        for offset in bytecode_offsets.into_iter().flatten() {
            self.add_start_bytecode_mapping(offset as i32);
        }
    }

    pub fn clear_unassigned_bytecode_mapping_data(&mut self) {
        self.bytecode_offset_mapping
            .retain(|key, _| key.class.is_some());
    }

    /// One tracer per class and method key, holding the line of every
    /// bytecode offset recorded for that method.
    pub fn get_tracers(&self) -> IndexMap<(String, Option<String>), BytecodeMappingTracer> {
        let separator = self.line_separator();
        let mut newline_offsets = Vec::new();
        let mut index = index_of(&self.text, &separator, 0);
        while index != -1 {
            newline_offsets.push(index);
            index = index_of(&self.text, &separator, index + 1);
        }

        let mut tracers: IndexMap<(String, Option<String>), BytecodeMappingTracer> =
            IndexMap::new();
        for (key, text_offset) in &self.bytecode_offset_mapping {
            let Some(class) = &key.class else {
                panic!(
                    "getTracers called when not all bytecode offsets have a valid class and method"
                );
            };
            let tracer = tracers
                .entry((class.clone(), key.method.clone()))
                .or_default();
            let line = newline_offsets
                .binary_search(text_offset)
                .unwrap_or_else(|insertion_point| insertion_point);
            tracer.set_current_source_line(line as i32);
            tracer.add_mapping(key.bytecode_offset);
        }
        tracers
    }

    /// Recursive reformatting of groups.
    /// If the group's content would take you over the specified preferred line
    /// length, then the group is applied.
    ///
    /// - This algorithm usually ensures that if a group is applied, then all
    ///   the group's parents in the tree are also applied. This tends to
    ///   produce a nice structured output with well-placed potential newlines.
    /// - The formatter keeps track of the offset as a result of the reformat
    ///   at each character in the text buffer, and applies them to the
    ///   bytecode offsets afterwards, so that the line number mappings don't
    ///   get messed up.
    fn reformat_group(
        &mut self,
        group: &mut NewlineGroup,
        offset_mapping: &mut Vec<i32>,
        mut extra_indent: i32,
    ) {
        let separator = self.line_separator();
        let separator_length = separator.len() as i32;
        let indent: Vec<u16> = self.options.indent_string.encode_utf16().collect();
        let indent_length = indent.len() as i32;

        let mut offset = offset_mapping[group.start as usize];
        let actual_start = group.start + offset;
        let group_end = actual_start + group.length;
        // Find the last newline before the start of this group, so we know how long the line already is
        let last_newline = last_index_of(&self.text, &separator, actual_start);
        let mut next_newline = index_of(&self.text, &separator, actual_start);
        // Find the end of the first line of this group, if the group were to not be reformatted
        let first_part_end = if next_newline == -1 {
            group_end
        } else {
            next_newline.min(group_end)
        };
        // Go through all lines in the group, and find the longest one (without reformatting)
        let mut group_end_without_newlines = if last_newline == -1 {
            first_part_end
        } else {
            first_part_end - last_newline
        };
        while next_newline != -1 && next_newline <= group_end {
            let line_start = next_newline;
            next_newline = index_of(&self.text, &separator, next_newline + 1);
            let line_end = if next_newline == -1 || next_newline > group_end {
                group_end
            } else {
                next_newline
            };
            let line_length = extra_indent + line_end - line_start - separator_length;
            group_end_without_newlines = group_end_without_newlines.max(line_length);
        }

        // If the longest line is longer than the preferred line length, then reformat the group
        let add_new_lines = group_end_without_newlines > self.options.preferred_line_length;
        let original_extra_indent = extra_indent;
        // If we're reformatting this group, and not only its children, then apply extra indentation
        if add_new_lines && !group.replacements.is_empty() {
            extra_indent += group.extra_indent;
        }

        // Iterate over the children and replacements in one go rather than separately, because
        // offsets need to be applied from left to right
        let mut children_index = 0;
        let mut replacement_index = 0;
        let mut pos = group.start;
        while pos <= group.start + group.length {
            if pos != group.start {
                offset_mapping.push(offset);
            }

            // add extra indent after newlines
            let after_separator = pos + offset + separator_length;
            if after_separator < self.length() && self.starts_with_at(&separator, pos + offset) {
                // not for blank lines
                let blank_line = after_separator + separator_length < self.length()
                    && self.starts_with_at(&separator, after_separator);
                if !blank_line {
                    self.insert_repeated(after_separator, &indent, extra_indent);
                    offset += indent_length * extra_indent;
                }
            }

            // do multiple passes in an inner loop, as there could be arbitrarily many with the
            // same offset or replacements with offsets equal to the end position of a child group
            let mut another_pass = true;
            while another_pass {
                another_pass = false;

                // replace replaceables with newlines
                if add_new_lines
                    && let Some(&replacement) = group.replacements.get(replacement_index)
                    && pos == replacement.start
                {
                    let at = (pos + offset) as usize;
                    self.text.splice(
                        at..at + replacement.length as usize,
                        separator.iter().copied(),
                    );
                    if replacement.dedent {
                        extra_indent = original_extra_indent;
                    }
                    let indents = group.base_indent + extra_indent;
                    self.insert_repeated(pos + offset + separator_length, &indent, indents);
                    offset += indent_length * indents + separator_length - replacement.length;
                    replacement_index += 1;
                    another_pass = true;
                }

                // offset may have changed, update the offset mapping here because the child
                // groups rely on the value being correct in the list
                *offset_mapping.last_mut().unwrap() = offset;

                // recursively iterate through child groups
                if let Some(child) = group.children.get_mut(children_index)
                    && child.start == pos
                {
                    self.reformat_group(child, offset_mapping, extra_indent);
                    offset = *offset_mapping.last().unwrap();
                    pos += child.length;
                    children_index += 1;
                    another_pass = true;
                }
            }

            pos += 1;
        }

        // update the offset value here because it might have changed when adding indents after
        // existing newlines; the parent relies on the value being correct in the list
        *offset_mapping.last_mut().unwrap() = offset;

        for token in &mut group.tokens {
            if let Some(&shift) = offset_mapping.get(token.start as usize) {
                token.shift(shift);
            }
        }
    }

    pub fn reformat(&mut self) {
        if !self.current_group.is_empty() {
            panic!("Cannot reformat while in a group");
        }
        if self.has_reformatted {
            panic!("Cannot reformat twice");
        }
        self.has_reformatted = true;

        self.root_group.length = self.length();
        let mut offset_mapping = Vec::with_capacity(self.text.len());
        offset_mapping.push(0);
        let mut root_group = std::mem::take(&mut self.root_group);
        self.reformat_group(&mut root_group, &mut offset_mapping, 0);
        self.root_group = root_group;
        for value in self.bytecode_offset_mapping.values_mut() {
            *value += offset_mapping[*value as usize];
        }
    }

    pub fn content_equals(&self, string: &str) -> bool {
        self.text.iter().copied().eq(string.encode_utf16())
    }

    /// The text, with the original line numbers of each line appended as a
    /// comment when they were supplied through
    /// [`dump_original_line_numbers`](Self::dump_original_line_numbers).
    pub fn convert_to_string_and_allow_data_discard(&self) -> String {
        match &self.line_mapping {
            Some(line_mapping) => self.add_original_line_numbers(line_mapping),
            None => String::from_utf16_lossy(&self.text),
        }
    }

    fn add_original_line_numbers(&self, line_mapping: &FxHashMap<i32, BTreeSet<i32>>) -> String {
        let separator = self.line_separator();
        let mut result: Vec<u16> = Vec::with_capacity(self.text.len());

        let mut line_start = 0;
        let mut count = 0;
        loop {
            // A separator at the very start of the text ends the scan, as upstream's `> 0` does.
            let line_end = index_of(&self.text, &separator, line_start);
            if line_end <= 0 {
                break;
            }
            count += 1;
            result.extend_from_slice(&self.text[line_start as usize..line_end as usize]);
            if let Some(lines) = line_mapping.get(&count) {
                result.extend("//".encode_utf16());
                for line in lines {
                    result.extend(format!(" {line}").encode_utf16());
                }
            }
            result.extend_from_slice(&separator);
            line_start = line_end + separator.len() as i32;
        }
        if line_start < self.length() {
            result.extend_from_slice(&self.text[line_start as usize..]);
        }

        String::from_utf16_lossy(&result)
    }

    pub fn length(&self) -> i32 {
        self.text.len() as i32
    }

    pub fn set_start(&mut self, position: i32) {
        self.text.drain(..position as usize);
        self.shift_mapping(-position);
    }

    pub fn set_length(&mut self, position: i32) {
        self.text.truncate(position as usize);
        self.root_group.truncate(position);
    }

    /// `append(TextBuffer, className, methodKey)`: appends a buffer whose
    /// unassigned bytecode offsets belong to the given method of the given class.
    pub fn append_buffer_for(
        &mut self,
        buffer: &TextBuffer,
        class_name: Option<&str>,
        method_key: Option<&str>,
    ) -> &mut Self {
        if !buffer.current_group.is_empty() {
            panic!("Can't append buffer with non-root group");
        }

        let length = self.length();
        for (key, value) in &buffer.bytecode_offset_mapping {
            let key = if key.class.is_none() {
                BytecodeMappingKey {
                    bytecode_offset: key.bytecode_offset,
                    class: class_name.map(str::to_owned),
                    method: method_key.map(str::to_owned),
                }
            } else {
                key.clone()
            };
            self.bytecode_offset_mapping
                .entry(key)
                .or_insert(value + length);
        }

        let mut other_root = buffer.root_group.clone();
        other_root.shift(length);
        let current = self.current_group_mut();
        current.replacements.append(&mut other_root.replacements);
        current.tokens.append(&mut other_root.tokens);
        current.children.append(&mut other_root.children);

        self.text.extend_from_slice(&buffer.text);
        self
    }

    /// `append(TextBuffer)`.
    pub fn append_buffer(&mut self, buffer: &TextBuffer) -> &mut Self {
        self.append_buffer_for(buffer, None, None)
    }

    fn shift_mapping(&mut self, shift_offset: i32) {
        for value in self.bytecode_offset_mapping.values_mut() {
            *value += shift_offset;
        }
        self.root_group.shift(shift_offset);
    }

    pub fn count_lines(&self) -> i32 {
        self.count_lines_from(0)
    }

    /// `countLines(from)`.
    pub fn count_lines_from(&self, from: i32) -> i32 {
        self.count(self.options.line_separator(), from)
    }

    /// The occurrences of `substring` from `from` on; one at the very start
    /// of the text ends the count, as upstream's `> 0` does.
    pub fn count(&self, substring: &str, from: i32) -> i32 {
        let pattern: Vec<u16> = substring.encode_utf16().collect();
        let mut count = 0;
        let mut position = index_of(&self.text, &pattern, from);
        while position > 0 {
            count += 1;
            position = index_of(&self.text, &pattern, position + pattern.len() as i32);
        }
        count
    }

    /// Records, for pairs of (original line, new line), the original lines to
    /// print at the end of each new line.
    pub fn dump_original_line_numbers(&mut self, line_mapping: &[i32]) {
        if line_mapping.is_empty() {
            return;
        }
        let mut mapping: FxHashMap<i32, BTreeSet<i32>> = FxHashMap::default();
        for pair in line_mapping.chunks_exact(2) {
            mapping.entry(pair[1]).or_default().insert(pair[0]);
        }
        self.line_mapping = Some(mapping);
    }

    /// The `line:column` of a position, both starting at one.
    pub fn get_pos(&self, index: i32) -> String {
        let separator = self.line_separator();
        let before = &self.text[..index as usize];
        let line = split_count(before, &separator);
        let line_start = match last_index_of(before, &separator, index) {
            -1 => 0,
            found => found + separator.len() as i32,
        };
        format!("{line}:{}", index + 1 - line_start)
    }

    pub fn get_tokens(&self) -> Vec<TextToken> {
        self.root_group.flatten_tokens()
    }

    pub fn visit_tokens(&self, visitor: &mut dyn TextTokenVisitor) {
        visitor.start(&String::from_utf16_lossy(&self.text));
        for token in self.get_tokens() {
            token.visit(visitor);
        }
        visitor.end();
    }

    fn line_separator(&self) -> Vec<u16> {
        self.options.line_separator().encode_utf16().collect()
    }

    fn starts_with_at(&self, pattern: &[u16], position: i32) -> bool {
        self.text[position as usize..].starts_with(pattern)
    }

    fn insert_repeated(&mut self, position: i32, pattern: &[u16], times: i32) {
        let position = position as usize;
        let repeated = pattern.repeat(times.max(0) as usize);
        self.text.splice(position..position, repeated);
    }
}

/// `indexOf(pattern, from)` on UTF-16 text: -1 if there is no occurrence.
fn index_of(text: &[u16], pattern: &[u16], from: i32) -> i32 {
    let from = (from.max(0) as usize).min(text.len());
    text[from..]
        .windows(pattern.len())
        .position(|window| window == pattern)
        .map_or(-1, |found| (from + found) as i32)
}

/// `lastIndexOf(pattern, from)`: the last occurrence starting at or before `from`.
fn last_index_of(text: &[u16], pattern: &[u16], from: i32) -> i32 {
    if from < 0 || pattern.len() > text.len() {
        return -1;
    }
    let last_start = (from as usize).min(text.len() - pattern.len());
    text[..last_start + pattern.len()]
        .windows(pattern.len())
        .rposition(|window| window == pattern)
        .map_or(-1, |found| found as i32)
}

/// `text.split(separator).length`: trailing empty parts do not count, and
/// text without any separator is one part even when it is empty.
fn split_count(text: &[u16], separator: &[u16]) -> usize {
    let mut parts = Vec::new();
    let mut start = 0;
    let mut position = index_of(text, separator, 0);
    while position != -1 {
        parts.push(position as usize - start);
        start = position as usize + separator.len();
        position = index_of(text, separator, start as i32);
    }
    if parts.is_empty() {
        return 1;
    }
    parts.push(text.len() - start);
    parts.len() - parts.iter().rev().take_while(|&&length| length == 0).count()
}
