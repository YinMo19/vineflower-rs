//! Vineflower's shortening of Java Float and Double strings for source output.

use crate::util::java_decimal;
use std::str::FromStr;

pub(super) fn float(value: f32) -> String {
    shorten(java_decimal::float(value), value, true)
}

pub(super) fn double(value: f64) -> String {
    shorten(java_decimal::double(value), value, false)
}

fn shorten<T: Copy + FromStr + PartialEq>(
    text: String,
    value: T,
    scientific_truncation: bool,
) -> String {
    if text.len() <= 3 {
        return text;
    }
    let exponent = text.find('E').unwrap_or(text.len());
    let (mut mantissa, suffix) = text.split_at(exponent);

    let round_trips = |text: &str| text.parse::<T>().is_ok_and(|parsed| parsed == value);
    while mantissa.len() > 1 {
        let shorter = &mantissa[..mantissa.len() - 1];
        if shorter == "-" {
            break;
        }
        // Vineflower checks Float prefixes with the exponent, and Double
        // prefixes as unscaled values. Rounded candidates always use it.
        let equal = if scientific_truncation && !suffix.is_empty() {
            round_trips(&format!("{shorter}{suffix}"))
        } else {
            round_trips(shorter)
        };
        if !equal {
            break;
        }
        mantissa = shorter;
    }

    let Some((whole, fraction)) = mantissa.split_once('.') else {
        return format!("{mantissa}.0{suffix}");
    };
    let next_integer = whole.parse::<i64>().unwrap() + 1;
    let integer_candidate = format!("{next_integer}.0{suffix}");
    if round_trips(&integer_candidate) {
        return integer_candidate;
    }

    let mut prefix = 0_u64;
    for digit in fraction.bytes().take(fraction.len().saturating_sub(1)) {
        prefix = prefix * 10 + u64::from(digit - b'0');
        let rounded = format!("{whole}.{}{suffix}", prefix + 1);
        if round_trips(&rounded) {
            return rounded;
        }
    }
    format!("{mantissa}{suffix}")
}
