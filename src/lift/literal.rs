// Copyright 2000-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use std::fmt::{Display, UpperExp, Write};

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
    constant_in_context(pool, index, expected, ascii, true)
}

fn constant_in_context(
    pool: &ConstantPool<'_>,
    index: u16,
    expected: Option<&Type>,
    ascii: bool,
    group_arithmetic: bool,
) -> Result<String, LiftError> {
    Ok(match pool.get(index)? {
        Constant::Integer(value) => integer_literal(*value, expected, ascii),
        Constant::Long(value) => format!("{value}L"),
        Constant::Float(value) => float_literal(*value, group_arithmetic),
        Constant::Double(value) => double_literal(*value, group_arithmetic),
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
    if !options.keep_literals
        && let Some(symbolic) = super::numeric::named(pool.get(index)?, expected, name)
    {
        return Ok(symbolic.text);
    }
    constant_in_context(pool, index, expected, options.ascii_strings, false)
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

pub(super) fn float_literal(value: f32, grouped: bool) -> String {
    if value.is_finite() {
        let magnitude = value.abs();
        finite_decimal(value, magnitude != 0.0 && !(1e-3..1e7).contains(&magnitude), "F")
    } else {
        exceptional_decimal(value.is_nan(), value.is_sign_negative(), "F", grouped)
    }
}

pub(super) fn double_literal(value: f64, grouped: bool) -> String {
    if value.is_finite() {
        let magnitude = value.abs();
        finite_decimal(value, magnitude != 0.0 && !(1e-3..1e7).contains(&magnitude), "")
    } else {
        exceptional_decimal(value.is_nan(), value.is_sign_negative(), "", grouped)
    }
}

fn finite_decimal(value: impl Display + UpperExp, scientific: bool, suffix: &str) -> String {
    // Rust's standard formatter supplies round-trippable shortest digits.
    // Java's spelling uses its own exponent threshold and a decimal point.
    let mut text = String::with_capacity(26);
    if scientific {
        let _ = write!(text, "{value:E}");
    } else {
        let _ = write!(text, "{value}");
    }
    if !text.contains('.') {
        let exponent = text.find('E').unwrap_or(text.len());
        text.insert_str(exponent, ".0");
    }
    text.push_str(suffix);
    text
}

fn exceptional_decimal(nan: bool, negative: bool, suffix: &str, grouped: bool) -> String {
    let numerator = if nan { "0.0" } else if negative { "-1.0" } else { "1.0" };
    if grouped {
        format!("({numerator}{suffix} / 0.0{suffix})")
    } else {
        format!("{numerator}{suffix} / 0.0{suffix}")
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

    #[test]
    fn floating_literals_preserve_subnormal_and_signed_zero_bits() {
        for (value, java) in [
            (f32::from_bits(1), "1.0E-45F"),
            (-0.0, "-0.0F"),
            (0.001, "0.001F"),
            (1e7, "1.0E7F"),
            (f32::MAX, "3.4028235E38F"),
        ] {
            let output = float_literal(value, false);
            assert_eq!(output, java);
            assert_eq!(
                output.strip_suffix('F').unwrap().parse::<f32>().unwrap().to_bits(),
                value.to_bits(),
            );
        }
        assert_eq!(double_literal(f64::from_bits(1), false), "5.0E-324");
        assert_eq!(double_literal(f64::INFINITY, true), "(1.0 / 0.0)");
        assert_eq!(float_literal(f32::NEG_INFINITY, false), "-1.0F / 0.0F");
    }
}
