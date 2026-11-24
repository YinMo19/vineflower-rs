// Based on Vineflower ConstExprent's constant uninlining (Apache-2.0).
// Copyright 2000-2021 JetBrains s.r.o.
use std::{collections::HashMap, f64::consts::{E, PI}, sync::LazyLock};

use num_integer::Integer;

use super::expr::{Expr, MULTIPLICATIVE, PRIMARY, UNARY};
use crate::{classfile::Constant, descriptor::{Primitive, Type}};

pub(super) struct Numeric {
    pub text: String,
    pub precedence: u8,
}

pub(super) fn expression(ty: Primitive, named: Option<Numeric>, literal: impl FnOnce() -> String) -> Expr {
    if let Some(named) = named {
        Expr { precedence: named.precedence, ..Expr::literal(Type::Primitive(ty), named.text) }
    } else {
        Expr::literal(Type::Primitive(ty), literal())
    }
}

pub(super) fn named(
    value: &Constant<'_>, expected: Option<&Type>, name: impl Fn(&str) -> String,
) -> Option<Numeric> {
    let field = |owner: &'static str, member: &'static str, negative: bool| Numeric {
        text: format!("{}{}.{member}", if negative { "-" } else { "" }, name(owner)),
        precedence: if negative { UNARY } else { PRIMARY },
    };
    Some(match value {
        Constant::Integer(value) if expected.is_none_or(|ty| *ty == Type::Primitive(Primitive::Int)) => {
            field("java/lang/Integer", extreme(*value, i32::MIN, i32::MAX)?, false)
        }
        Constant::Long(value) => field("java/lang/Long", extreme(*value, i64::MIN, i64::MAX)?, false),
        Constant::Float(value) => {
            if let Some((member, negative)) = floating_field(*value, f32::MAX, f32::MIN_POSITIVE, f32::from_bits(1)) {
                field("java/lang/Float", member, negative)
            } else {
                angles().1.get(&value.to_bits())?.render(&name("java/lang/Math"))
            }
        }
        Constant::Double(value) => {
            if let Some((member, negative)) = floating_field(*value, f64::MAX, f64::MIN_POSITIVE, f64::from_bits(1)) {
                field("java/lang/Double", member, negative)
            } else {
                angles().0.get(&value.to_bits())?.render(&name("java/lang/Math"))
            }
        }
        _ => return None,
    })
}

fn extreme<T: Eq>(value: T, min: T, max: T) -> Option<&'static str> {
    if value == min { Some("MIN_VALUE") } else if value == max { Some("MAX_VALUE") } else { None }
}

fn floating_field<T: Into<f64> + Copy>(value: T, max: T, normal: T, min: T) -> Option<(&'static str, bool)> {
    let value = value.into();
    if value.is_nan() { return Some(("NaN", false)); }
    if value == f64::INFINITY { return Some(("POSITIVE_INFINITY", false)); }
    if value == f64::NEG_INFINITY { return Some(("NEGATIVE_INFINITY", false)); }
    let positive = value.abs();
    let member = if positive == max.into() { "MAX_VALUE" }
        else if positive == normal.into() { "MIN_NORMAL" }
        else if positive == min.into() { "MIN_VALUE" }
        else { return None; };
    Some((member, value.is_sign_negative()))
}

#[derive(Clone, Copy)]
enum Formula {
    E,
    Pi,
    DivInt(u8),
    MulInt(u8),
    Fraction(u8, u8),
    DegreesPerRadian,
    RadiansPerDegree,
}

#[derive(Clone, Copy)]
enum Cast {
    None,
    Whole,
    Pi,
}

#[derive(Clone, Copy)]
struct Angle {
    formula: Formula,
    negative: bool,
    cast: Cast,
}

impl Angle {
    fn render(self, math: &str) -> Numeric {
        let sign = if self.negative { "-" } else { "" };
        let mut text = match (self.formula, self.cast) {
            (Formula::E, _) => format!("{sign}{math}.E"),
            (Formula::Pi, _) => format!("{sign}{math}.PI"),
            (Formula::DivInt(den), _) => format!("{sign}{math}.PI / {den}"),
            (Formula::MulInt(num), _) => format!("{sign}{math}.PI * {num}"),
            (Formula::Fraction(num, den), Cast::Pi) => format!("(float) {sign}{math}.PI * {num}.0F / {den}.0F"),
            (Formula::Fraction(num, den), _) => format!("{sign}{math}.PI * {num}.0 / {den}.0"),
            (Formula::DegreesPerRadian, Cast::Pi) => format!("{sign}180.0F / (float){math}.PI"),
            (Formula::DegreesPerRadian, _) => format!("{sign}180.0 / {math}.PI"),
            (Formula::RadiansPerDegree, _) => format!("{sign}{math}.PI / 180.0"),
        };
        let atomic = matches!(self.formula, Formula::Pi | Formula::E);
        let precedence = match self.cast {
            Cast::Whole => {
                text = if atomic { format!("(float) {text}") } else { format!("(float) ({text})") };
                UNARY
            }
            _ if !atomic => MULTIPLICATIVE,
            _ if self.negative => UNARY,
            _ => PRIMARY,
        };
        Numeric { text, precedence }
    }
}

type Angles = (HashMap<u64, Angle>, HashMap<u32, Angle>);

fn angles() -> &'static Angles {
    static ANGLES: LazyLock<Angles> = LazyLock::new(|| {
        let (mut doubles, mut floats) = Angles::default();
        let mut double = |value: f64, formula| {
            for negative in [false, true] {
                let value = if negative { -value } else { value };
                let angle = Angle { formula, negative, cast: Cast::None };
                doubles.insert(value.to_bits(), angle);
                floats.insert((value as f32).to_bits(), Angle { cast: Cast::Whole, ..angle });
            }
        };
        double(E, Formula::E);
        double(PI, Formula::Pi);
        for denominator in 2..=20 {
            double(PI / f64::from(denominator), Formula::DivInt(denominator));
        }
        for numerator in 2..=20 {
            double(PI * f64::from(numerator), Formula::MulInt(numerator));
        }
        for numerator in 2u8..13 {
            for denominator in 2u8..13 {
                if numerator.gcd(&denominator) == 1 {
                    // Use only values whose printed Java expression has exactly
                    // the same IEEE 754 rounding as the class-file constant.
                    double(PI * f64::from(numerator) / f64::from(denominator), Formula::Fraction(numerator, denominator));
                }
            }
        }
        double(180.0 / PI, Formula::DegreesPerRadian);
        double(PI / 180.0, Formula::RadiansPerDegree);
        let mut rounded_pi = |value: f32, formula| {
            for negative in [false, true] {
                let value = if negative { -value } else { value };
                floats.entry(value.to_bits()).or_insert(Angle { formula, negative, cast: Cast::Pi });
            }
        };
        rounded_pi(180.0f32 / PI as f32, Formula::DegreesPerRadian);
        for numerator in 2u8..13 {
            for denominator in 2u8..13 {
                if numerator.gcd(&denominator) == 1 {
                    rounded_pi(PI as f32 * f32::from(numerator) / f32::from(denominator), Formula::Fraction(numerator, denominator));
                }
            }
        }
        (doubles, floats)
    });
    &ANGLES
}
