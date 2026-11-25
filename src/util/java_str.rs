// SPDX-License-Identifier: Apache-2.0

//! Operations of `java.lang.String` whose results differ from those of
//! their Rust look-alikes.

use std::sync::Arc;

use arcstr::ArcStr;
use itertools::Either;

use super::jhash::JavaHash;

/// A Java string constant. Values represent UTF-16 code units, including
/// isolated surrogates. Ordinary strings share the same UTF-8 storage used
/// for names and descriptors throughout the class model.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct JavaString(Repr);

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Repr {
    Utf8(ArcStr),
    Unpaired(Arc<Unpaired>),
}

#[derive(Debug, PartialEq, Eq, Hash)]
struct Unpaired {
    units: Box<[u16]>,
    display: ArcStr,
}

impl JavaString {
    pub fn from_utf16(units: Vec<u16>) -> Self {
        match String::from_utf16(&units) {
            Ok(text) => Self::from(text),
            Err(_) => Self(Repr::Unpaired(Arc::new(Unpaired {
                display: String::from_utf16_lossy(&units).into(),
                units: units.into_boxed_slice(),
            }))),
        }
    }

    /// The UTF-8 view used by existing symbol APIs. Render literals, hash
    /// strings, and index Java text through `utf16` to preserve every unit.
    pub fn as_utf8_lossy(&self) -> &ArcStr {
        match &self.0 {
            Repr::Utf8(text) => text,
            Repr::Unpaired(raw) => &raw.display,
        }
    }

    pub fn utf16(&self) -> impl Iterator<Item = u16> + '_ {
        match &self.0 {
            Repr::Utf8(text) => Either::Left(text.encode_utf16()),
            Repr::Unpaired(raw) => Either::Right(raw.units.iter().copied()),
        }
    }
}

impl<T: Into<ArcStr>> From<T> for JavaString {
    fn from(text: T) -> Self {
        Self(Repr::Utf8(text.into()))
    }
}

impl JavaHash for JavaString {
    fn java_hash(&self) -> i32 {
        self.utf16().fold(0i32, |hash, unit| {
            hash.wrapping_mul(31).wrapping_add(i32::from(unit))
        })
    }
}

/// `String.length()`: the number of UTF-16 units in `text`.
pub fn utf16_len(text: &str) -> i32 {
    if text.is_ascii() {
        text.len() as i32
    } else {
        text.encode_utf16().count() as i32
    }
}

/// `String.split(separator)` for a literal separator: empty parts at the end
/// are dropped, and text without any separator is one part even when empty.
pub fn split<'a>(text: &'a str, separator: &str) -> Vec<&'a str> {
    if !text.contains(separator) {
        return vec![text];
    }
    let mut parts: Vec<&str> = text.split(separator).collect();
    while parts.last() == Some(&"") {
        parts.pop();
    }
    parts
}
