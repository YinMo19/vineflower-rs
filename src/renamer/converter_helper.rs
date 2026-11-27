//! The default IdentifierRenamer, with counters shared across class loading.

use rustc_hash::FxHashSet;
use unicode_general_category::{GeneralCategory, get_general_category};

use super::{IdentifierKind, IdentifierRenamer};
use crate::code::code_constants::{CLINIT_NAME, INIT_NAME};
use crate::util::text_util::{
    is_java_identifier_ignorable, is_java_identifier_part, is_java_identifier_start,
    is_reserved_word,
};

#[derive(Default)]
pub struct ConverterHelper {
    class_counter: i32,
    field_counter: i32,
    method_counter: i32,
    nonstandard_names: FxHashSet<String>,
}

impl IdentifierRenamer for ConverterHelper {
    fn to_be_renamed(
        &mut self,
        kind: IdentifierKind,
        class_name: &str,
        element: Option<&str>,
        _descriptor: Option<&str>,
    ) -> bool {
        let name = if kind == IdentifierKind::Class {
            Some(class_name)
        } else {
            element
        };
        let Some(name) = name else { return true };
        let reserved_windows = is_windows_reserved(name);
        !valid_identifier(name, kind == IdentifierKind::Method)
            || is_reserved_word(name)
            || name == "enum"
            || (!reserved_windows && obfuscated_name(name))
            || (kind == IdentifierKind::Class
                && (reserved_windows || name.encode_utf16().count() > 249))
    }

    fn next_class_name(&mut self, _name: &str, simple: Option<&str>) -> String {
        let Some(simple) = simple else {
            return next("class_", &mut self.class_counter);
        };
        let suffix = simple.trim_start_matches(|ch: char| {
            ch.len_utf16() == 1 && get_general_category(ch) == GeneralCategory::DecimalNumber
        });
        if suffix.len() == simple.len() || suffix.is_empty() {
            next("class_", &mut self.class_counter)
        } else if self.nonstandard_names.insert(suffix.to_owned()) {
            format!("Inner{suffix}")
        } else {
            next(&format!("Inner{suffix}_"), &mut self.class_counter)
        }
    }

    fn next_field_name(&mut self, _class: &str, _field: &str, _descriptor: &str) -> String {
        next("field_", &mut self.field_counter)
    }

    fn next_method_name(&mut self, _class: &str, _method: &str, _descriptor: &str) -> String {
        next("method_", &mut self.method_counter)
    }
}

pub(super) fn simple_class_name(name: &str) -> &str {
    name.rsplit('/').next().unwrap()
}

pub(super) fn replace_simple_class_name(name: &str, simple: &str) -> String {
    if let Some((package, _)) = name.rsplit_once('/') {
        format!("{package}/{simple}")
    } else {
        simple.to_owned()
    }
}

fn next(prefix: &str, counter: &mut i32) -> String {
    let name = format!("{prefix}{counter}");
    *counter = counter.wrapping_add(1);
    name
}

fn valid_identifier(name: &str, method: bool) -> bool {
    if method && matches!(name, INIT_NAME | CLINIT_NAME) {
        return true;
    }
    let mut units = name.encode_utf16();
    units.next().is_some_and(is_java_identifier_start)
        && units.all(|unit| is_java_identifier_part(unit) && !is_java_identifier_ignorable(unit))
}

fn is_windows_reserved(name: &str) -> bool {
    let lower = name.to_ascii_lowercase();
    matches!(lower.as_str(), "con" | "prn" | "aux" | "nul")
        || matches!(
            lower.as_bytes(),
            [b'c', b'o', b'm', b'1'..=b'9'] | [b'l', b'p', b't', b'1'..=b'9']
        )
}

fn obfuscated_name(name: &str) -> bool {
    // ConverterHelper's ^(?:.{1,3}(?:$|\$))+ lets a dollar sign
    // occur as a separator or inside one of the short segments.
    if !name.contains('$') {
        return (1..=3).contains(&name.chars().take(4).count());
    }
    let mut starts = vec![false; name.len() + 1];
    starts[0] = true;
    for (start, _) in name.char_indices() {
        if !starts[start] {
            continue;
        }
        for (offset, ch) in name[start..].char_indices().take(3) {
            let end = start + offset + ch.len_utf8();
            if end == name.len() {
                return true;
            }
            if name.as_bytes()[end] == b'$' {
                starts[end + 1] = true;
            }
        }
    }
    starts[name.len()]
}
