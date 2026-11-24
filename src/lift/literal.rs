// Copyright 2000-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use std::fmt::Write;

use crate::{
    Options,
    classfile::{Constant, ConstantPool},
    descriptor::{Primitive, Type},
};

use super::LiftError;

pub(crate) fn constant_literal(
    pool: &ConstantPool<'_>,
    index: u16,
    expected: Option<&Type>,
    ascii: bool,
) -> Result<String, LiftError> {
    Ok(match pool.get(index)? {
        Constant::Integer(value) => integer_literal(*value, expected, ascii),
        Constant::Long(value) => format!("{value}L"),
        Constant::Float(value) => float_literal(*value),
        Constant::Double(value) => double_literal(*value),
        Constant::String(index) => string_literal(&pool.utf16(*index)?, ascii),
        Constant::Utf8(text) => string_literal(&text.utf16(), ascii),
        _ => return Err(LiftError::UnrepresentableConstant(index)),
    })
}

pub(crate) fn constant_literal_with_options(
    pool: &ConstantPool<'_>,
    index: u16,
    expected: Option<&Type>,
    options: &Options,
    name: impl Fn(&str) -> String,
) -> Result<String, LiftError> {
    if !options.keep_literals && let Some(symbolic) = super::numeric::named(pool.get(index)?, expected, name) {
        return Ok(symbolic.text);
    }
    constant_literal(pool, index, expected, options.ascii_strings)
}

pub(super) fn integer_literal(value: i32, expected: Option<&Type>, ascii: bool) -> String {
    match expected {
        Some(Type::Primitive(Primitive::Boolean)) => ((value & 1) != 0).to_string(),
        Some(Type::Primitive(Primitive::Byte)) => (value as i8).to_string(),
        Some(Type::Primitive(Primitive::Short)) => (value as i16).to_string(),
        Some(Type::Primitive(Primitive::Char)) => quoted(&[value as u16], '\'', ascii),
        _ => value.to_string(),
    }
}

pub(super) fn float_literal(value: f32) -> String {
    if value.is_nan() {
        "(0.0F / 0.0F)".into()
    } else if value.is_infinite() {
        if value.is_sign_negative() {
            "(-1.0F / 0.0F)"
        } else {
            "(1.0F / 0.0F)"
        }
        .into()
    } else {
        format!("{value:?}F")
    }
}

pub(super) fn double_literal(value: f64) -> String {
    if value.is_nan() {
        "(0.0 / 0.0)".into()
    } else if value.is_infinite() {
        if value.is_sign_negative() {
            "(-1.0 / 0.0)"
        } else {
            "(1.0 / 0.0)"
        }
        .into()
    } else {
        format!("{value:?}")
    }
}

pub(crate) fn string_literal(units: &[u16], ascii: bool) -> String {
    quoted(units, '"', ascii)
}

fn quoted(units: &[u16], quote: char, ascii: bool) -> String {
    let mut result = String::with_capacity(units.len() + 2);
    result.push(quote);
    for ch in char::decode_utf16(units.iter().copied()) {
        match ch {
            Ok('\u{8}') => result.push_str("\\b"),
            Ok('\t') => result.push_str("\\t"),
            Ok('\n') => result.push_str("\\n"),
            Ok('\u{c}') => result.push_str("\\f"),
            Ok('\r') => result.push_str("\\r"),
            Ok('\\') => result.push_str("\\\\"),
            Ok(ch) if ch == quote => {
                result.push('\\');
                result.push(ch);
            }
            Ok(ch) if ch.is_control() && (ch as u32) <= 0x7f => {
                let _ = write!(result, "\\{:03o}", ch as u32);
            }
            Ok(ch) if ch.is_control() || (ascii && !ch.is_ascii()) => {
                for &mut unit in ch.encode_utf16(&mut [0; 2]) {
                    let _ = write!(result, "\\u{unit:04x}");
                }
            }
            Ok(ch) => result.push(ch),
            Err(err) => {
                let _ = write!(result, "\\u{:04x}", err.unpaired_surrogate());
            }
        }
    }
    result.push(quote);
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn quotes_java_utf16_without_losing_units() {
        assert_eq!(
            string_literal(&[0, 0x37, 0x22, 0x5c, 0xa, 0xd800], true),
            r#""\0007\"\\\n\ud800""#
        );
        let units = [0xd83d, 0xde00];
        assert_eq!(string_literal(&units, true), r#""\ud83d\ude00""#);
        assert_eq!(string_literal(&units, false), "\"😀\"");
        assert_eq!(
            integer_literal(0x27, Some(&Type::Primitive(Primitive::Char)), false),
            "'\\''"
        );
    }
}
