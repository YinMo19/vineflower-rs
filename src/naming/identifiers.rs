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

#[cfg(test)]
mod tests {
    use super::{IdentifierKind::*, *};

    #[test]
    fn converter_helper_contract() {
        let cases = [
            (
                Some("ValidClassName"),
                Some("validFieldName"),
                Some("validMethodName"),
                [false; 3],
            ),
            (None, None, None, [true; 3]),
            (Some(""), Some(""), Some(""), [true; 3]),
            (Some("C"), Some("f"), Some("m"), [true; 3]),
            (Some("_"), Some("_"), Some("_"), [true; 3]),
            (Some("public"), Some("public"), Some("public"), [true; 3]),
            (Some("nul"), Some("nul"), Some("nul"), [true, false, false]),
            (
                Some("4identifier"),
                Some("4identifier"),
                Some("4identifier"),
                [true; 3],
            ),
            (
                Some("\u{feff}ClassName"),
                Some("\u{feff}fieldName"),
                Some("\u{feff}methodName"),
                [true; 3],
            ),
            (
                Some("Class\u{feff}Name"),
                Some("field\u{feff}Name"),
                Some("method\u{feff}Name"),
                [true; 3],
            ),
            (
                Some("ClassName\u{feff}"),
                Some("fieldName\u{feff}"),
                Some("methodName\u{feff}"),
                [true; 3],
            ),
            (
                Some("<init>"),
                Some("<init>"),
                Some("<init>"),
                [true, true, false],
            ),
            (
                Some("<clinit>"),
                Some("<clinit>"),
                Some("<clinit>"),
                [true, true, false],
            ),
        ];
        for (class, field, method, expected) in cases {
            for ((kind, name), result) in [(Class, class), (Field, field), (Method, method)]
                .into_iter()
                .zip(expected)
            {
                assert_eq!(
                    MemberRenamer::to_be_renamed(kind, name),
                    result,
                    "{kind:?}: {name:?}"
                );
            }
        }
    }

    #[test]
    fn java_categories_and_keyword_context() {
        for name in [
            "€value",
            "_value",
            "‿value",
            "Ⅻvalue",
            "a\u{300}\u{903}٢",
            "日本語",
            "a$b",
        ] {
            assert!(is_valid_identifier(Field, name), "{name:?}");
        }
        for name in [
            "٢value",
            "\u{300}value",
            "a²",
            "a·b",
            "a\u{200d}b",
            "a\u{7f}b",
            "a\0b",
            "𐐀value",
        ] {
            assert!(!is_valid_identifier(Field, name), "{name:?}");
        }
        assert!(is_valid_local_identifier("enum", 48));
        assert!(!is_valid_local_identifier("enum", 49));
        assert!(is_valid_local_identifier("_", 52));
        assert!(!is_valid_local_identifier("_", 53));
        assert!(is_valid_local_identifier("var", 69));
        assert!(!is_valid_local_identifier("this", 52));
    }

    #[test]
    fn short_components_windows_names_and_class_file_length() {
        for name in ["a", "a$bb$c", "a$", "$a$$$def"] {
            assert!(MemberRenamer::to_be_renamed(Class, Some(name)), "{name}");
        }
        for name in ["$abc", "abc$$def", "abcd$a", "a$abcd"] {
            assert!(!MemberRenamer::to_be_renamed(Class, Some(name)), "{name}");
        }
        for name in ["CoN", "COM1", "Lpt9"] {
            assert!(MemberRenamer::to_be_renamed(Class, Some(name)), "{name}");
            assert!(!MemberRenamer::to_be_renamed(Method, Some(name)), "{name}");
        }
        assert!(!MemberRenamer::to_be_renamed(Class, Some("com0")));
        assert!(!MemberRenamer::to_be_renamed(Class, Some(&"é".repeat(249))));
        assert!(MemberRenamer::to_be_renamed(Class, Some(&"é".repeat(250))));
        assert!(!MemberRenamer::to_be_renamed(Field, Some(&"é".repeat(250))));
    }

    #[test]
    fn generated_names_avoid_collisions_and_keep_independent_counters() {
        let mut renamer = MemberRenamer::default();
        assert_eq!(
            renamer.next_available(Class, Some("٢foo"), |name| name == "Innerfoo"),
            "Innerfoo_0"
        );
        assert_eq!(renamer.next_name(Class, Some("3foo")), "Innerfoo_1");
        assert_eq!(renamer.next_name(Class, Some("7")), "class_2");
        assert_eq!(
            renamer.next_available(Field, Some("f"), |name| name == "field_0"),
            "field_1"
        );
        assert_eq!(renamer.next_name(Method, Some("m")), "method_0");
    }
}
