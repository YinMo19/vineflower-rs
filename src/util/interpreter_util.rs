//! `util.InterpreterUtil` and `util.IntHelper`.
//!
//! The helpers that are a single standard operation in Rust have no
//! counterpart here: `equalObjects` and `equalLists` are `==` (on `Option`s and
//! slices alike), `ArrayHelper.containsByRef` is `contains` on a slice of
//! handles, `copyFile`, `copyStream` and `getBytes(File)` are `std::fs::copy`,
//! `std::io::copy` and `std::fs::read`, and `getBytes(ZipFile, ZipEntry)` is
//! [`read_bytes`] on the entry's reader.

use std::io::{self, Read};

/// Exactly `length` bytes of `stream`.
pub fn read_bytes(stream: &mut impl Read, length: usize) -> io::Result<Vec<u8>> {
    let mut bytes = Vec::with_capacity(length);
    stream.take(length as u64).read_to_end(&mut bytes)?;
    if bytes.len() < length {
        return Err(premature_end_of_stream());
    }
    Ok(bytes)
}

pub fn discard_bytes(stream: &mut impl Read, length: u64) -> io::Result<()> {
    if io::copy(&mut stream.take(length), &mut io::sink())? != length {
        return Err(premature_end_of_stream());
    }
    Ok(())
}

fn premature_end_of_stream() -> io::Error {
    io::Error::new(io::ErrorKind::UnexpectedEof, "premature end of stream")
}

/// True if the collections have the same length and every element of `c1`
/// occurs in `c2`. For collections with repeated elements that is weaker than
/// set equality.
pub fn equal_sets<T: PartialEq>(c1: &[T], c2: &[T]) -> bool {
    c1.len() == c2.len() && c1.iter().all(|element| c2.contains(element))
}

pub fn make_unique_key(name: &str, descriptor: &str) -> String {
    format!("{name} {descriptor}")
}

/// `makeUniqueKey(name, descriptor1, descriptor2)`.
pub fn make_unique_key3(name: &str, descriptor1: &str, descriptor2: &str) -> String {
    format!("{name} {descriptor1} {descriptor2}")
}

/// `IntHelper.adjustedIntRepresentation`: the text of an int constant, with
/// the masks of the components of an RGB color written in hexadecimal.
pub fn adjusted_int_representation(value: i32) -> String {
    match value as u32 {
        0xFF => "0xFF".to_owned(),
        0xFF00 => "0xFF00".to_owned(),
        0xFF0000 => "0xFF0000".to_owned(),
        0xFF000000 => "0xFF000000".to_owned(),
        _ => value.to_string(),
    }
}
