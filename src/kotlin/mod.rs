// SPDX-License-Identifier: Apache-2.0

//! The Kotlin language plugin bundled with Vineflower.

pub mod imports;
pub mod types;

use std::borrow::Cow;

use crate::util::text_util::is_java_identifier;

/// KotlinWriter.toValidKotlinIdentifier, including its spelling of quoted names.
pub fn identifier(name: &str) -> Cow<'_, str> {
    let keyword = matches!(
        name,
        "as" | "break"
            | "class"
            | "continue"
            | "do"
            | "else"
            | "false"
            | "for"
            | "fun"
            | "if"
            | "in"
            | "interface"
            | "is"
            | "null"
            | "object"
            | "package"
            | "return"
            | "super"
            | "this"
            | "throw"
            | "true"
            | "try"
            | "typealias"
            | "typeof"
            | "val"
            | "var"
            | "when"
            | "while"
    );
    if name.is_empty() || (!keyword && !name.contains('$') && is_java_identifier(name)) {
        return Cow::Borrowed(name);
    }
    let quoted = format!("`{}`", name.replace('`', "_"));
    if name.contains('`') {
        format!("{quoted} /* $VF was: {quoted} */").into()
    } else {
        quoted.into()
    }
}
