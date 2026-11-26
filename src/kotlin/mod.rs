// SPDX-License-Identifier: Apache-2.0

//! The Kotlin language plugin bundled with Vineflower.

pub mod body;
pub mod declarations;
pub mod imports;
pub mod member_writer;
pub mod members;
pub mod metadata;
pub mod passes;
pub mod types;
pub mod writer;

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

/// MethodProcessor's Kotlin LanguageSpec runs its CFG, method and final AST passes in order.
pub(crate) fn code_to_kotlin(
    cx: &mut crate::engine::Cx,
    class: &crate::structs::StructClass,
    method: &std::sync::Arc<crate::structs::StructMethod>,
) -> std::io::Result<Option<crate::engine::method_processor::ExpressionMethod>> {
    let Some(mut result) = passes::defined_method(cx, class, method)? else {
        return Ok(None);
    };
    body::prepare(cx, &mut result)?;
    Ok(Some(result))
}
