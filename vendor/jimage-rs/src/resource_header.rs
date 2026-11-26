// SPDX-License-Identifier: MIT

use crate::bytes_utils::read_integer_mut;
use crate::error::{internal, JImageError, Result};
use crate::jimage::Endianness;

const MAGIC: u32 = 0xcafe_fafa;
const HEADER_SIZE: usize = 29;

pub(crate) struct CompressedResource<'a> {
    pub(crate) payload: &'a [u8],
    pub(crate) output_size: usize,
    pub(crate) decompressor: usize,
}

impl<'a> CompressedResource<'a> {
    pub(crate) fn begins(bytes: &[u8], endianness: &Endianness) -> bool {
        let magic = match endianness {
            Endianness::Big => MAGIC.to_be_bytes(),
            Endianness::Little => MAGIC.to_le_bytes(),
        };
        bytes.len() >= HEADER_SIZE && bytes.starts_with(&magic)
    }

    pub(crate) fn read(bytes: &'a [u8], endianness: &Endianness) -> Result<Self> {
        let payload = bytes.get(HEADER_SIZE..).ok_or(JImageError::RawRead {
            from: 0,
            to: HEADER_SIZE,
        })?;
        if !Self::begins(bytes, endianness) {
            return Err(JImageError::Magic {
                magic: bytes[..4].try_into()?,
                context: "resource",
            });
        }
        let mut offset = 4;
        let size: u64 = read_integer_mut(bytes, &mut offset, endianness)?;
        let output_size: u64 = read_integer_mut(bytes, &mut offset, endianness)?;
        let decompressor: u32 = read_integer_mut(bytes, &mut offset, endianness)?;
        if usize::try_from(size).ok() != Some(payload.len()) {
            return Err(internal(
                "JImage compressed resource size does not match its header",
            ));
        }
        // The two built-in decompressors have no configuration. The JDK
        // detects subsequent layers by their magic, regardless of isTerminal.
        Ok(Self {
            payload,
            output_size: usize::try_from(output_size)
                .map_err(|_| internal("JImage expanded resource size exceeds address space"))?,
            decompressor: decompressor as usize,
        })
    }
}
