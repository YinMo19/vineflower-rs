//! The decimal spelling produced by the Java 17 Float and Double wrappers.

use num_bigint::BigUint;
use num_integer::Integer;
use std::cmp::Ordering;

pub(crate) fn float(value: f32) -> String {
    if !value.is_finite() {
        return non_finite(value.is_nan(), value.is_sign_negative()).to_owned();
    }
    java_decimal(
        u64::from(value.to_bits() & 0x7fff_ffff),
        23,
        127,
        value.is_sign_negative(),
    )
}

pub(crate) fn double(value: f64) -> String {
    if !value.is_finite() {
        return non_finite(value.is_nan(), value.is_sign_negative()).to_owned();
    }
    java_decimal(
        value.to_bits() & 0x7fff_ffff_ffff_ffff,
        52,
        1023,
        value.is_sign_negative(),
    )
}

fn non_finite(nan: bool, negative: bool) -> &'static str {
    if nan {
        "NaN"
    } else if negative {
        "-Infinity"
    } else {
        "Infinity"
    }
}

// JDK 17 uses this rounded coefficient in its decimal exponent estimate.
#[allow(
    clippy::approx_constant,
    reason = "the rounded coefficient controls JDK 17's first digit"
)]
const LOG10_2_ESTIMATE: f64 = 0.301029995663981;

fn java_decimal(bits: u64, fraction_bits: i32, bias: i32, negative: bool) -> String {
    if bits == 0 {
        return if negative { "-0.0" } else { "0.0" }.to_owned();
    }
    let hidden = 1_u64 << fraction_bits;
    let encoded_exponent = (bits >> fraction_bits) as i32;
    let fraction = bits & (hidden - 1);
    let mantissa = if encoded_exponent == 0 {
        fraction
    } else {
        fraction | hidden
    };
    let mantissa_bits = mantissa.ilog2() as i32 + 1;
    let exponent = if encoded_exponent == 0 {
        mantissa_bits - fraction_bits - bias
    } else {
        encoded_exponent - bias
    };

    let coefficient = mantissa >> mantissa.trailing_zeros();
    let coefficient_bits = coefficient.ilog2() as i32 + 1;
    let binary_scale = exponent + 1 - coefficient_bits;
    let decimal = if binary_scale >= 0 && exponent <= 62 {
        Decimal::integral(coefficient << binary_scale, exponent, mantissa_bits)
    } else {
        // JDK 17 uses a symmetric half-ULP margin. It halves that margin
        // at exact powers of two, including subnormals.
        let margin_scale = exponent - mantissa_bits - i32::from(coefficient == 1);
        let unit_mantissa = mantissa as f64 / (1_u64 << (mantissa_bits - 1)) as f64;
        // This tangent to log10 supplies JDK 17's starting decade. A
        // leading zero corrects an overestimate during digit extraction.
        let decade = ((unit_mantissa - 1.5) * 0.289529654
            + 0.176091259
            + f64::from(exponent) * LOG10_2_ESTIMATE)
            .floor() as i32;
        Decimal::fractional(coefficient, binary_scale, margin_scale, decade)
    };
    decimal.format(negative)
}

struct Decimal {
    digits: String,
    /// Base-10 exponent of the first digit.
    decade: i32,
}

impl Decimal {
    fn integral(value: u64, binary_exponent: i32, precision: i32) -> Self {
        // The integral fast path rounds to a decimal unit smaller than the
        // binary spacing. Its half-way rule here is to round upward.
        let bits_to_discard = binary_exponent - precision - 1;
        let places = if bits_to_discard > 1 {
            (1_u64 << bits_to_discard).ilog10()
        } else {
            0
        };
        let rounded = if places == 0 {
            value
        } else {
            let unit = 10_u64.pow(places);
            value / unit + u64::from(value % unit >= unit / 2)
        };
        let digits = rounded.to_string();
        Self {
            decade: digits.len() as i32 - 1 + places as i32,
            digits: digits.trim_end_matches('0').to_owned(),
        }
    }

    fn fractional(coefficient: u64, scale: i32, margin_scale: i32, mut decade: i32) -> Self {
        let mut ratio = DigitRatio::new(coefficient, scale, margin_scale, decade);
        let mut integer = 0_u64;
        let mut count = 0;
        let mut first = true;
        loop {
            let digit = ratio.next_digit(first);
            if first && digit.value == 0 && !digit.upper {
                decade -= 1;
            } else {
                integer = integer * 10 + u64::from(digit.value);
                count += 1;
            }

            // In compatibility mode the old converter collects extra
            // precision on the first step outside this decade range.
            let needs_second = first && !(-3..8).contains(&decade);
            first = false;
            if needs_second || (!digit.lower && !digit.upper) {
                continue;
            }

            if digit.upper
                && (!digit.lower
                    || digit.midpoint == Ordering::Greater
                    || (digit.midpoint == Ordering::Equal && !integer.is_multiple_of(2)))
            {
                integer += 1;
                if integer == 10_u64.pow(count) {
                    integer /= 10;
                    decade += 1;
                }
            }
            return Self {
                digits: format!("{integer:0width$}", width = count as usize),
                decade,
            };
        }
    }

    fn format(&self, negative: bool) -> String {
        let mut output = String::new();
        if negative {
            output.push('-');
        }
        let digits = &self.digits;
        match self.decade {
            0..=6 => {
                let before_point = self.decade as usize + 1;
                let (whole, fraction) = digits.split_at(digits.len().min(before_point));
                output.push_str(whole);
                output.extend(std::iter::repeat_n('0', before_point - whole.len()));
                output.push('.');
                output.push_str(if fraction.is_empty() { "0" } else { fraction });
            }
            -3..=-1 => {
                output.push_str("0.");
                output.extend(std::iter::repeat_n('0', (-1 - self.decade) as usize));
                output.push_str(digits);
            }
            _ => {
                let (whole, fraction) = digits.split_at(1);
                output.push_str(whole);
                output.push('.');
                output.push_str(if fraction.is_empty() { "0" } else { fraction });
                output.push('E');
                output.push_str(&self.decade.to_string());
            }
        }
        output
    }
}

/// To generate decimal digits, normalize the value to B/S and track M/S,
/// its stopping margin. B, S and M stay integers after a shared shift.
struct Ratio<T> {
    remainder: T,
    divisor: T,
    margin: T,
    decade_divisor: T,
}

enum DigitRatio {
    Word { ratio: Ratio<i64>, narrow: bool },
    Big(Ratio<BigUint>),
}

struct Digit {
    value: u32,
    lower: bool,
    upper: bool,
    midpoint: Ordering,
}

impl DigitRatio {
    fn new(coefficient: u64, scale: i32, margin_scale: i32, decade: i32) -> Self {
        let numerator_fives = (-decade).max(0) as u32;
        let denominator_fives = decade.max(0) as u32;
        let numerator_twos = scale + numerator_fives as i32;
        let denominator_twos = denominator_fives as i32;
        let margin_twos = margin_scale + numerator_fives as i32;
        let common = numerator_twos.min(denominator_twos).min(margin_twos);
        let numerator_shift = (numerator_twos - common) as u32;
        let denominator_shift = (denominator_twos - common) as u32;
        let margin_shift = (margin_twos - common) as u32;

        let numerator_width =
            coefficient.ilog2() + 1 + numerator_shift + power_of_five_width(numerator_fives);
        let decade_width = denominator_shift + 1 + power_of_five_width(denominator_fives + 1);
        let width = numerator_width.max(decade_width);
        if width < 64 {
            let numerator_power = 5_i64.pow(numerator_fives);
            let divisor = 5_i64.pow(denominator_fives) << denominator_shift;
            Self::Word {
                ratio: Ratio {
                    remainder: (coefficient as i64 * numerator_power) << numerator_shift,
                    divisor,
                    margin: numerator_power << margin_shift,
                    decade_divisor: divisor * 10,
                },
                narrow: width < 32,
            }
        } else {
            let five = BigUint::from(5_u8);
            let numerator_power = five.pow(numerator_fives);
            let divisor = five.pow(denominator_fives) << denominator_shift;
            Self::Big(Ratio {
                remainder: (&numerator_power * coefficient) << numerator_shift,
                margin: numerator_power << margin_shift,
                decade_divisor: &divisor * 10_u8,
                divisor,
            })
        }
    }

    fn next_digit(&mut self, first: bool) -> Digit {
        match self {
            DigitRatio::Word { ratio, narrow } => {
                let word = |v: i64| if *narrow { i64::from(v as i32) } else { v };
                let value = (ratio.remainder / ratio.divisor) as u32;
                ratio.remainder = (ratio.remainder % ratio.divisor) * 10;
                ratio.margin = word(ratio.margin.wrapping_mul(10));
                // Preserve the signed overflow and the strict upper boundary
                // of both native-width branches of JDK 17.
                let overflow = !first && ratio.margin <= 0;
                let lower = overflow || ratio.remainder < ratio.margin;
                let upper = overflow
                    || word(ratio.remainder.wrapping_add(ratio.margin)) > ratio.decade_divisor;
                let midpoint = word(
                    ratio
                        .remainder
                        .wrapping_mul(2)
                        .wrapping_sub(ratio.decade_divisor),
                )
                .cmp(&0);
                Digit {
                    value,
                    lower,
                    upper,
                    midpoint,
                }
            }
            DigitRatio::Big(ratio) => {
                let (quotient, remainder) = ratio.remainder.div_rem(&ratio.divisor);
                ratio.remainder = remainder * 10_u8;
                ratio.margin *= 10_u8;
                let lower = ratio.remainder < ratio.margin;
                let upper = &ratio.remainder + &ratio.margin >= ratio.decade_divisor;
                let midpoint = (&ratio.remainder << 1_u32).cmp(&ratio.decade_divisor);
                let value = quotient.iter_u32_digits().next().unwrap_or(0);
                Digit {
                    value,
                    lower,
                    upper,
                    midpoint,
                }
            }
        }
    }
}

fn power_of_five_width(exponent: u32) -> u32 {
    match exponent {
        0 => 0,
        1..=26 => 5_u64.pow(exponent).ilog2() + 1,
        _ => exponent * 3,
    }
}
