// Copyright 2000-2017 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use std::collections::HashSet;

use unicode_general_category::{GeneralCategory, get_general_category};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum IdentifierKind {
    Class,
    Field,
    Method,
}

/// Character-level validation used by Vineflower's ConverterHelper. This is
/// deliberately independent of keywords and the short-name renaming heuristic.
/// Like the original `char` overloads, it rejects supplementary characters, and
/// unlike `Character.isJavaIdentifierPart` it rejects ignorable characters.
pub fn is_valid_identifier(kind: IdentifierKind, name: &str) -> bool {
    if kind == IdentifierKind::Method && matches!(name, "<init>" | "<clinit>") {
        return true;
    }
    let mut chars = name.chars();
    chars.next().is_some_and(identifier_start) && chars.all(identifier_part)
}

fn identifier_start(ch: char) -> bool {
    if ch.is_ascii() {
        return ch.is_ascii_alphabetic() || matches!(ch, '$' | '_');
    }
    ch.len_utf16() == 1 && identifier_start_category(get_general_category(ch))
}

fn identifier_start_category(category: GeneralCategory) -> bool {
    matches!(
        category,
        GeneralCategory::UppercaseLetter
            | GeneralCategory::LowercaseLetter
            | GeneralCategory::TitlecaseLetter
            | GeneralCategory::ModifierLetter
            | GeneralCategory::OtherLetter
            | GeneralCategory::LetterNumber
            | GeneralCategory::CurrencySymbol
            | GeneralCategory::ConnectorPunctuation
    )
}

fn identifier_part(ch: char) -> bool {
    if ch.is_ascii() {
        return ch.is_ascii_alphanumeric() || matches!(ch, '$' | '_');
    }
    if ch.len_utf16() != 1 {
        return false;
    }
    let category = get_general_category(ch);
    identifier_start_category(category)
        || matches!(
            category,
            GeneralCategory::NonspacingMark
                | GeneralCategory::SpacingMark
                | GeneralCategory::DecimalNumber
        )
}

/// Checks whether a debug or generated name can be written as a Java local.
pub fn is_valid_local_identifier(name: &str, major_version: u16) -> bool {
    !local_keyword(name, major_version) && is_valid_identifier(IdentifierKind::Field, name)
}

pub(super) fn local_keyword(name: &str, major_version: u16) -> bool {
    keyword(name) || (major_version >= 49 && name == "enum") || (major_version >= 53 && name == "_")
}

fn keyword(name: &str) -> bool {
    matches!(
        name,
        "abstract"
            | "assert"
            | "boolean"
            | "break"
            | "byte"
            | "case"
            | "catch"
            | "char"
            | "class"
            | "const"
            | "continue"
            | "default"
            | "do"
            | "double"
            | "else"
            | "extends"
            | "false"
            | "final"
            | "finally"
            | "float"
            | "for"
            | "goto"
            | "if"
            | "implements"
            | "import"
            | "instanceof"
            | "int"
            | "interface"
            | "long"
            | "native"
            | "new"
            | "null"
            | "package"
            | "private"
            | "protected"
            | "public"
            | "return"
            | "short"
            | "static"
            | "strictfp"
            | "super"
            | "switch"
            | "synchronized"
            | "this"
            | "throw"
            | "throws"
            | "transient"
            | "true"
            | "try"
            | "void"
            | "volatile"
            | "while"
    )
}

fn windows_reserved(name: &str) -> bool {
    let bytes = name.as_bytes();
    match bytes {
        [_, _, _] => [b"con", b"prn", b"aux", b"nul"]
            .iter()
            .any(|reserved| bytes.eq_ignore_ascii_case(*reserved)),
        [prefix @ .., b'1'..=b'9'] if prefix.len() == 3 => {
            prefix.eq_ignore_ascii_case(b"com") || prefix.eq_ignore_ascii_case(b"lpt")
        }
        _ => false,
    }
}

// ^(?:.{1,3}(?:$|\$))+$ after identifier validation. Bit k means a
// segmentation is possible whose current component contains k characters.
fn short_obfuscated(name: &str) -> bool {
    let mut lengths = 1u8;
    for ch in name.chars() {
        let separator = ch == '$' && lengths & 0b1110 != 0;
        lengths = ((lengths << 1) & 0b1111) | u8::from(separator);
        if lengths == 0 {
            return false;
        }
    }
    true
}

/// One session's ConverterHelper counters. Callers supply the applicable class
/// or member namespace, so declarations and references can use the same names.
#[derive(Debug, Default)]
pub struct MemberRenamer {
    class_counter: u32,
    field_counter: u32,
    method_counter: u32,
    numeric_class_stems: HashSet<String>,
}

impl MemberRenamer {
    /// Whether Vineflower's default `rename-members` policy selects this name.
    /// For a class, pass the simple binary name without the package prefix.
    pub fn to_be_renamed(kind: IdentifierKind, name: Option<&str>) -> bool {
        let Some(name) = name else { return true };
        if !is_valid_identifier(kind, name) || keyword(name) || name == "enum" {
            return true;
        }
        let reserved = windows_reserved(name);
        (!reserved && short_obfuscated(name))
            || (kind == IdentifierKind::Class
                && (reserved || (name.len() > 249 && name.encode_utf16().count() > 249)))
    }

    /// Generates the next policy candidate, without testing for collisions.
    /// `original` is only used for numeric prefixes on simple class names.
    pub fn next_name(&mut self, kind: IdentifierKind, original: Option<&str>) -> String {
        match kind {
            IdentifierKind::Class => {
                if let Some(name) = original {
                    let stem = name.trim_start_matches(|ch: char| {
                        ch.len_utf16() == 1
                            && get_general_category(ch) == GeneralCategory::DecimalNumber
                    });
                    if !stem.is_empty() && stem.len() != name.len() {
                        if self.numeric_class_stems.contains(stem) {
                            let suffix = self.class_counter;
                            self.class_counter += 1;
                            return format!("Inner{stem}_{suffix}");
                        }
                        self.numeric_class_stems.insert(stem.into());
                        return format!("Inner{stem}");
                    }
                }
                numbered("class", &mut self.class_counter)
            }
            IdentifierKind::Field => numbered("field", &mut self.field_counter),
            IdentifierKind::Method => numbered("method", &mut self.method_counter),
        }
    }

    /// Gets a candidate that does not collide with the caller's namespace.
    pub fn next_available(
        &mut self,
        kind: IdentifierKind,
        original: Option<&str>,
        mut is_taken: impl FnMut(&str) -> bool,
    ) -> String {
        loop {
            let name = self.next_name(kind, original);
            if !is_taken(&name) {
                return name;
            }
        }
    }
}

fn numbered(prefix: &str, counter: &mut u32) -> String {
    let next = format!("{prefix}_{counter}");
    *counter += 1;
    next
}
