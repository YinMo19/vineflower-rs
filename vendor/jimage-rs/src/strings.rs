// SPDX-License-Identifier: MIT

use crate::error::{internal, JImageError, Result};
use memchr::memchr;
use std::borrow::Cow;

#[derive(Clone, Copy)]
pub(crate) struct StringTable<'a>(pub(crate) &'a [u8]);

impl<'a> StringTable<'a> {
    pub(crate) fn bytes(self, index: usize) -> Result<&'a [u8]> {
        let remainder = self
            .0
            .get(index..)
            .ok_or_else(|| internal("String offset outside jimage string table"))?;
        let end = memchr(0, remainder).ok_or_else(|| internal("Unterminated jimage string"))?;
        Ok(&remainder[..end])
    }

    pub(crate) fn name(self, index: usize) -> Result<Cow<'a, str>> {
        let bytes = self.bytes(index)?;
        match std::str::from_utf8(bytes) {
            Ok(text) => Ok(Cow::Borrowed(text)),
            Err(source) => {
                decode_modified_utf8(bytes)
                    .map(Cow::Owned)
                    .ok_or_else(|| JImageError::Utf8 {
                        source,
                        invalid_data: bytes.to_vec(),
                    })
            }
        }
    }
}

fn decode_modified_utf8(bytes: &[u8]) -> Option<String> {
    let mut units = Vec::new();
    let mut remaining = bytes;
    while let Some((&first, rest)) = remaining.split_first() {
        let (unit, rest) = match first {
            0x01..=0x7f => (u16::from(first), rest),
            0xc0..=0xdf => {
                let (&second, rest) = rest.split_first()?;
                let unit = (u16::from(first & 0x1f) << 6) | continuation(second)?;
                if unit != 0 && unit < 0x80 {
                    return None;
                }
                (unit, rest)
            }
            0xe0..=0xef => {
                let (&second, rest) = rest.split_first()?;
                let (&third, rest) = rest.split_first()?;
                let unit = (u16::from(first & 0x0f) << 12)
                    | (continuation(second)? << 6)
                    | continuation(third)?;
                if unit < 0x800 {
                    return None;
                }
                (unit, rest)
            }
            _ => return None,
        };
        units.push(unit);
        remaining = rest;
    }
    String::from_utf16(&units).ok()
}

fn continuation(byte: u8) -> Option<u16> {
    (byte & 0xc0 == 0x80).then_some(u16::from(byte & 0x3f))
}

const HASH_MULTIPLIER: u32 = 0x01000193;
pub(crate) const HASH_SEED: i32 = HASH_MULTIPLIER as i32;

/// JImage hashes the Modified UTF-8 encoding of the Java string.
pub(crate) fn hash(name: &str, seed: i32) -> usize {
    let mut hash = seed as u32;
    let mut push = |byte| {
        hash = hash.wrapping_mul(HASH_MULTIPLIER) ^ u32::from(byte);
    };
    if name.is_ascii() && !name.as_bytes().contains(&0) {
        for &byte in name.as_bytes() {
            push(byte);
        }
    } else {
        for unit in name.encode_utf16() {
            match unit {
                1..=0x7f => push(unit as u8),
                0..=0x7ff => {
                    push(0xc0 | (unit >> 6) as u8);
                    push(0x80 | (unit & 0x3f) as u8);
                }
                _ => {
                    push(0xe0 | (unit >> 12) as u8);
                    push(0x80 | ((unit >> 6) & 0x3f) as u8);
                    push(0x80 | (unit & 0x3f) as u8);
                }
            }
        }
    }
    (hash & 0x7fff_ffff) as usize
}
