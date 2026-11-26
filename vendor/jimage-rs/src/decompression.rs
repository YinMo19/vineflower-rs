// SPDX-License-Identifier: MIT

use crate::{
    error::{internal, DecompressionSnafu, JImageError, Result},
    jimage::Endianness,
    resource_header::CompressedResource,
    strings::StringTable,
};
use snafu::ResultExt;
use std::{borrow::Cow, io::Read};

pub(crate) fn resource(
    bytes: &[u8],
    expected_size: usize,
    strings: StringTable<'_>,
    endianness: &Endianness,
) -> Result<Vec<u8>> {
    let mut input = Cow::Borrowed(bytes);
    loop {
        let layer = CompressedResource::read(&input, endianness)?;
        let output = match strings.bytes(layer.decompressor)? {
            b"zip" => unzip(layer.payload, layer.output_size)?,
            b"compact-cp" => expand_class(layer.payload, layer.output_size, strings)?,
            name => {
                return Err(JImageError::UnsupportedDecompressor {
                    decompressor_name: String::from_utf8_lossy(name).into_owned(),
                })
            }
        };
        if output.len() != layer.output_size {
            return Err(internal(
                "JImage expanded resource size does not match its header",
            ));
        }
        if !CompressedResource::begins(&output, endianness) {
            if output.len() != expected_size {
                return Err(internal(
                    "JImage expanded resource size does not match its location",
                ));
            }
            return Ok(output);
        }
        if output.as_slice() == input.as_ref() {
            return Err(internal("JImage resource decompressor did not advance"));
        }
        input = Cow::Owned(output);
    }
}

fn unzip(bytes: &[u8], expected_size: usize) -> Result<Vec<u8>> {
    let mut result = Vec::with_capacity(expected_size.min(bytes.len()));
    let limit = (expected_size as u64).saturating_add(1);
    flate2::bufread::ZlibDecoder::new(bytes)
        .take(limit)
        .read_to_end(&mut result)
        .context(DecompressionSnafu)?;
    Ok(result)
}

const CLASS_HEADER_SIZE: usize = 10;
const UTF8: u8 = 1;
const EXTERNAL_STRING: u8 = 23;
const EXTERNAL_DESCRIPTOR: u8 = 25;

fn expand_class(
    mut input: &[u8],
    expected_size: usize,
    strings: StringTable<'_>,
) -> Result<Vec<u8>> {
    let header = read(&mut input, CLASS_HEADER_SIZE)?;
    if !header.starts_with(&[0xca, 0xfe, 0xba, 0xbe]) {
        return Err(internal("JImage compact-cp resource is not a class file"));
    }
    let count = u16::from_be_bytes(header[8..10].try_into()?);
    if count == 0 {
        return Err(internal(
            "JImage compact-cp class has no constant pool count",
        ));
    }
    let mut output = Bytes::new(expected_size, input.len());
    output.append(header)?;
    let mut slot = 1;
    while slot < count {
        let tag = read(&mut input, 1)?[0];
        slot += 1;
        match tag {
            EXTERNAL_STRING => output.utf8(strings.bytes(index(&mut input)?)?)?,
            EXTERNAL_DESCRIPTOR => {
                let template = strings.bytes(index(&mut input)?)?;
                let length = index(&mut input)?;
                let indices = read(&mut input, length)?;
                output.utf8(&descriptor(template, indices, strings)?)?;
            }
            UTF8 => {
                let length = u16::from_be_bytes(read(&mut input, 2)?.try_into()?);
                output.utf8(read(&mut input, usize::from(length))?)?;
            }
            _ => {
                let width = match tag {
                    // Class, String, MethodType, Module, Package.
                    7 | 8 | 16 | 19 | 20 => 2,
                    // MethodHandle.
                    15 => 3,
                    // Integer, Float, references, NameAndType, Dynamic, InvokeDynamic.
                    3 | 4 | 9..=12 | 17 | 18 => 4,
                    5 | 6 => {
                        if slot == count {
                            return Err(internal(
                                "JImage compact-cp two-slot constant exceeds the constant pool",
                            ));
                        }
                        slot += 1;
                        8
                    }
                    _ => {
                        return Err(internal(format!(
                            "Unknown JImage compact-cp constant tag {tag}"
                        )))
                    }
                };
                output.append(&[tag])?;
                output.append(read(&mut input, width)?)?;
            }
        }
    }
    output.append(input)?;
    Ok(output.data)
}

fn descriptor(template: &[u8], mut indices: &[u8], strings: StringTable<'_>) -> Result<Vec<u8>> {
    // Each L placeholder takes a package and local class name from the index stream.
    let mut output = Bytes::new(usize::from(u16::MAX), template.len());
    for section in template.split_inclusive(|&byte| byte == b'L') {
        output.append(section)?;
        if section.ends_with(b"L") {
            let package = strings.bytes(index(&mut indices)?)?;
            let class = strings.bytes(index(&mut indices)?)?;
            if !package.is_empty() {
                output.append(package)?;
                output.append(b"/")?;
            }
            output.append(class)?;
        }
    }
    if !indices.is_empty() {
        return Err(internal("Unused JImage compact-cp descriptor indices"));
    }
    Ok(output.data)
}

fn index(input: &mut &[u8]) -> Result<usize> {
    let header = read(input, 1)?[0];
    let (length, mut value) = if header & 0x80 == 0 {
        (4, usize::from(header))
    } else {
        let length = usize::from((header >> 5) & 3);
        if length == 0 {
            return Err(internal("Invalid JImage compact-cp index width"));
        }
        (length, usize::from(header & 0x1f))
    };
    for &byte in read(input, length - 1)? {
        value = (value << 8) | usize::from(byte);
    }
    Ok(value)
}

fn read<'a>(input: &mut &'a [u8], size: usize) -> Result<&'a [u8]> {
    if size > input.len() {
        return Err(internal("Truncated JImage compact-cp constant pool"));
    }
    let (bytes, rest) = input.split_at(size);
    *input = rest;
    Ok(bytes)
}

struct Bytes {
    data: Vec<u8>,
    limit: usize,
}

impl Bytes {
    fn new(limit: usize, capacity_hint: usize) -> Self {
        Self {
            data: Vec::with_capacity(limit.min(capacity_hint)),
            limit,
        }
    }

    fn append(&mut self, bytes: &[u8]) -> Result<()> {
        if bytes.len() > self.limit - self.data.len() {
            return Err(internal("JImage compact-cp data exceeds its declared size"));
        }
        self.data.extend_from_slice(bytes);
        Ok(())
    }

    fn utf8(&mut self, bytes: &[u8]) -> Result<()> {
        let length = u16::try_from(bytes.len())
            .map_err(|_| internal("JImage compact-cp UTF-8 constant is too long"))?;
        self.append(&[UTF8])?;
        self.append(&length.to_be_bytes())?;
        self.append(bytes)
    }
}
