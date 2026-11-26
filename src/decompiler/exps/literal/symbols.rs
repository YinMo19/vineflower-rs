// Copyright 2000-2018 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Constant expressions reconstructed from the value of the inlined field.

use super::{BytecodeOffsets, Cx, FieldDescriptor, TextBuffer, static_field};
use num_integer::Integer;
use rustc_hash::FxHashMap;
use std::{
    f64::consts::{E, PI},
    sync::LazyLock,
};

#[derive(Clone, Copy)]
pub(super) struct Field {
    owner: &'static str,
    name: &'static str,
    descriptor: &'static str,
}

impl Field {
    const fn new(owner: &'static str, name: &'static str, descriptor: &'static str) -> Self {
        Self {
            owner,
            name,
            descriptor,
        }
    }

    pub(super) const fn integer(name: &'static str) -> Self {
        Self::new("java/lang/Integer", name, "Ljava/lang/Integer;")
    }
    pub(super) const fn long(name: &'static str) -> Self {
        Self::new("java/lang/Long", name, "Ljava/lang/Long;")
    }
    const fn float(name: &'static str) -> Self {
        Self::new("java/lang/Float", name, "Ljava/lang/Float;")
    }
    const fn double(name: &'static str) -> Self {
        Self::new("java/lang/Double", name, "Ljava/lang/Double;")
    }
    const fn math(name: &'static str) -> Self {
        Self::new("java/lang/Math", name, "Ljava/lang/Double;")
    }

    fn buffer(self, cx: &mut Cx, offsets: Option<&BytecodeOffsets>) -> TextBuffer {
        // ConstExprent materializes a temporary FieldExprent even when only
        // precedence is requested. Its ID shares the active expression counter.
        cx.expression_ids.next();
        static_field(
            cx,
            self.owner,
            self.name,
            &FieldDescriptor::parse_descriptor(self.descriptor),
            offsets,
        )
    }

    pub(super) fn write(
        self,
        cx: &mut Cx,
        buf: &mut TextBuffer,
        offsets: Option<&BytecodeOffsets>,
    ) {
        buf.append_buffer(&self.buffer(cx, offsets));
    }
}

#[derive(Clone)]
struct Symbol {
    field: Field,
    prefix: String,
    suffix: String,
}

impl Symbol {
    fn new(field: Field, before: &str, after: &str) -> Self {
        Self {
            field,
            prefix: before.to_owned(),
            suffix: after.to_owned(),
        }
    }

    fn negative(&self) -> Self {
        Self {
            prefix: format!("-{}", self.prefix),
            ..self.clone()
        }
    }

    fn cast_to_float(&self) -> Self {
        let mut copy = self.clone();
        if copy.prefix.contains(' ') || copy.suffix.contains(' ') {
            copy.prefix.insert(0, '(');
            copy.suffix.push(')');
        }
        copy.prefix.insert_str(0, "(float) ");
        copy
    }

    fn buffer(&self, cx: &mut Cx, offsets: Option<&BytecodeOffsets>) -> TextBuffer {
        let mut buf = self.field.buffer(cx, offsets);
        buf.prepend(&self.prefix).append(&self.suffix);
        buf
    }
}

#[derive(Default)]
struct Symbols {
    doubles: FxHashMap<u64, Symbol>,
    floats: FxHashMap<u32, Symbol>,
}

impl Symbols {
    fn double_pair(&mut self, value: f64, symbol: Symbol) {
        self.doubles.insert((-value).to_bits(), symbol.negative());
        self.doubles.insert(value.to_bits(), symbol);
    }

    fn float_pair(&mut self, value: f32, symbol: Symbol) {
        self.floats.insert((-value).to_bits(), symbol.negative());
        self.floats.insert(value.to_bits(), symbol);
    }
}

static SYMBOLS: LazyLock<Symbols> = LazyLock::new(|| {
    let mut symbols = Symbols::default();
    let pi = Field::math("PI");
    symbols.double_pair(E, Symbol::new(Field::math("E"), "", ""));
    symbols.double_pair(PI, Symbol::new(pi, "", ""));
    for factor in 2..=20 {
        symbols.double_pair(
            PI / f64::from(factor),
            Symbol::new(pi, "", &format!(" / {factor}")),
        );
        symbols.double_pair(
            PI * f64::from(factor),
            Symbol::new(pi, "", &format!(" * {factor}")),
        );
    }

    for numerator in 2i32..=12 {
        for denominator in 2i32..=12 {
            if numerator.gcd(&denominator) != 1 {
                continue;
            }
            let (n, d) = (f64::from(numerator), f64::from(denominator));
            symbols.double_pair(
                PI * (n / d),
                Symbol::new(pi, "", &format!(" * {numerator}.0 / {denominator}.0")),
            );

            let (nf, df) = (numerator as f32, denominator as f32);
            if (PI as f32) * nf / df != (PI * n / d) as f32 {
                let suffix = format!(" * {numerator}.0F / {denominator}.0F");
                for (sign, prefix) in [(1.0f32, "(float) "), (-1.0, "(float) -")] {
                    symbols.floats.insert(
                        (sign * (PI as f32) * (nf / df)).to_bits(),
                        Symbol::new(pi, prefix, &suffix),
                    );
                }
            }
        }
    }

    symbols.double_pair(180.0 / PI, Symbol::new(pi, "180.0 / ", ""));
    symbols.float_pair((180.0 / PI) as f32, Symbol::new(pi, "180.0F / ", ""));
    symbols.float_pair(
        180.0f32 / (PI as f32),
        Symbol::new(pi, "180.0F / (float)", ""),
    );
    symbols.double_pair(PI / 180.0, Symbol::new(pi, "", " / 180.0"));
    for (sign, prefix) in [(1.0f64, "(float) "), (-1.0, "(float) -")] {
        symbols.floats.insert(
            ((sign * PI / 180.0) as f32).to_bits(),
            Symbol::new(pi, prefix, " / 180.0"),
        );
    }

    // The casts of distinct double formulas in this table have distinct
    // float values. These entries take precedence over the earlier float forms.
    for (&bits, symbol) in &symbols.doubles {
        symbols.floats.insert(
            (f64::from_bits(bits) as f32).to_bits(),
            symbol.cast_to_float(),
        );
    }

    for (name, d, f) in [
        ("MAX_VALUE", f64::MAX, f32::MAX),
        ("MIN_NORMAL", f64::MIN_POSITIVE, f32::MIN_POSITIVE),
        ("MIN_VALUE", f64::from_bits(1), f32::from_bits(1)),
    ] {
        symbols.double_pair(d, Symbol::new(Field::double(name), "", ""));
        symbols.float_pair(f, Symbol::new(Field::float(name), "", ""));
    }
    for (name, d, f) in [
        ("POSITIVE_INFINITY", f64::INFINITY, f32::INFINITY),
        ("NEGATIVE_INFINITY", f64::NEG_INFINITY, f32::NEG_INFINITY),
    ] {
        symbols
            .doubles
            .insert(d.to_bits(), Symbol::new(Field::double(name), "", ""));
        symbols
            .floats
            .insert(f.to_bits(), Symbol::new(Field::float(name), "", ""));
    }
    symbols
});

pub(super) fn write_double(
    cx: &mut Cx,
    buf: &mut TextBuffer,
    value: f64,
    offsets: Option<&BytecodeOffsets>,
) -> bool {
    if value.is_nan() {
        Field::double("NaN").write(cx, buf, offsets);
    } else if let Some(symbol) = SYMBOLS.doubles.get(&value.to_bits()) {
        buf.append_buffer(&symbol.buffer(cx, offsets));
    } else {
        return false;
    }
    true
}

pub(super) fn write_float(
    cx: &mut Cx,
    buf: &mut TextBuffer,
    value: f32,
    offsets: Option<&BytecodeOffsets>,
) -> bool {
    if value.is_nan() {
        Field::float("NaN").write(cx, buf, offsets);
    } else if let Some(symbol) = SYMBOLS.floats.get(&value.to_bits()) {
        buf.append_buffer(&symbol.buffer(cx, offsets));
    } else {
        return false;
    }
    true
}

/// ConstExprent.getPrecedence looks at the rendered symbol, including any float cast.
pub fn precedence(
    cx: &mut Cx,
    ty: &crate::types::VarType,
    value: &super::ConstantValue,
    offsets: Option<&BytecodeOffsets>,
) -> i32 {
    use super::ConstantValue;
    use crate::types::CodeType;
    if cx.options.keep_literals {
        return 0;
    }
    let ty = ty.unboxing_type().map_or(ty.ty, |t| t.ty);
    let symbol = match (ty, value) {
        (CodeType::Double, ConstantValue::Double(x)) if x.abs() != E && x.abs() != PI => {
            SYMBOLS.doubles.get(&x.to_bits())
        }
        (CodeType::Float, ConstantValue::Float(x))
            if x.abs() != E as f32 && x.abs() != PI as f32 =>
        {
            SYMBOLS.floats.get(&x.to_bits())
        }
        _ => None,
    };
    if symbol.is_some_and(|s| s.buffer(cx, offsets).count_chars(u16::from(b'(')) < 2) {
        4
    } else {
        0
    }
}
