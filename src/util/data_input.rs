// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! `util.DataInputFullStream`: big-endian reads from the bytes of a class
//! file, with the operations of `java.io.DataInputStream` that upstream uses.

use std::io;

use super::java_str::JavaString;

pub struct DataInputFullStream<'a> {
    bytes: &'a [u8],
}

impl<'a> DataInputFullStream<'a> {
    pub fn new(bytes: &'a [u8]) -> Self {
        Self { bytes }
    }

    fn take<const N: usize>(&mut self) -> io::Result<[u8; N]> {
        let (head, rest) = self
            .bytes
            .split_first_chunk::<N>()
            .ok_or(io::ErrorKind::UnexpectedEof)?;
        self.bytes = rest;
        Ok(*head)
    }

    pub fn read_byte(&mut self) -> io::Result<i8> {
        self.take().map(i8::from_be_bytes)
    }

    pub fn read_unsigned_byte(&mut self) -> io::Result<i32> {
        self.take().map(|bytes| i32::from(u8::from_be_bytes(bytes)))
    }

    pub fn read_short(&mut self) -> io::Result<i16> {
        self.take().map(i16::from_be_bytes)
    }

    pub fn read_unsigned_short(&mut self) -> io::Result<i32> {
        self.take()
            .map(|bytes| i32::from(u16::from_be_bytes(bytes)))
    }

    pub fn read_int(&mut self) -> io::Result<i32> {
        self.take().map(i32::from_be_bytes)
    }

    pub fn read_long(&mut self) -> io::Result<i64> {
        self.take().map(i64::from_be_bytes)
    }

    pub fn read_float(&mut self) -> io::Result<f32> {
        self.take().map(f32::from_be_bytes)
    }

    pub fn read_double(&mut self) -> io::Result<f64> {
        self.take().map(f64::from_be_bytes)
    }

    /// `read(n)` and `readFully`: the next `n` bytes.
    pub fn read(&mut self, n: i32) -> io::Result<&'a [u8]> {
        let (head, rest) = self
            .bytes
            .split_at_checked(n as usize)
            .ok_or(io::ErrorKind::UnexpectedEof)?;
        self.bytes = rest;
        Ok(head)
    }

    pub fn discard(&mut self, n: i32) -> io::Result<()> {
        self.read(n).map(drop)
    }

    /// `skipBytes(n)`, which stops quietly at the end of the data.
    pub fn skip_bytes(&mut self, n: i32) {
        let n = (n.max(0) as usize).min(self.bytes.len());
        self.bytes = &self.bytes[n..];
    }

    /// UTF-8 view for callers that need a Rust string.
    pub fn read_utf(&mut self) -> io::Result<String> {
        Ok(self.read_java_utf()?.as_utf8_lossy().to_string())
    }

    /// `DataInputStream.readUTF` on a class file. Each encoded character
    /// contributes one UTF-16 code unit, including an unpaired surrogate.
    pub fn read_java_utf(&mut self) -> io::Result<JavaString> {
        let length = self.read_unsigned_short()?;
        let bytes = self.read(length)?;
        if bytes.is_ascii() {
            return Ok(std::str::from_utf8(bytes).unwrap().into());
        }

        let malformed = || io::Error::new(io::ErrorKind::InvalidData, "malformed input");
        let continuation = |byte: Option<&u8>| match byte {
            Some(&byte) if byte & 0xC0 == 0x80 => Ok(u16::from(byte & 0x3F)),
            _ => Err(malformed()),
        };

        let mut units = Vec::with_capacity(bytes.len());
        let mut rest = bytes.iter();
        while let Some(&first) = rest.next() {
            units.push(match first >> 4 {
                0..=7 => u16::from(first),
                12 | 13 => u16::from(first & 0x1F) << 6 | continuation(rest.next())?,
                14 => {
                    let second = continuation(rest.next())?;
                    u16::from(first & 0x0F) << 12 | second << 6 | continuation(rest.next())?
                }
                _ => return Err(malformed()),
            });
        }
        Ok(JavaString::from_utf16(units))
    }
}
