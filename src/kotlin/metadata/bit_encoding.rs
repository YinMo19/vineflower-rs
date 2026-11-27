//! Decode the bytes embedded in the metadata annotation's d1 strings.

use crate::util::java_str::JavaString;

/// Uses Java char narrowing, including on unpaired UTF-16 surrogates. The
/// marker is inspected only in the first string.
pub fn decode_bytes(strings: &[JavaString]) -> Vec<u8> {
    let marker = strings.first().and_then(|string| string.utf16().next());
    let marked = matches!(marker, Some(0 | 0xffff));
    let units = strings
        .iter()
        .enumerate()
        .flat_map(|(index, string)| string.utf16().skip(usize::from(index == 0 && marked)));
    if marker == Some(0) {
        return units.map(|unit| unit as u8).collect();
    }

    // Undo addModuloByte and concatenate the seven significant bits of each
    // byte, starting at the least significant end. Padding is discarded.
    let mut result = Vec::new();
    let mut pending = 0u16;
    let mut bits = 0;
    for unit in units {
        let decoded = ((unit as u8).wrapping_sub(1)) & 0x7f;
        pending |= u16::from(decoded) << bits;
        bits += 7;
        if bits >= 8 {
            result.push(pending as u8);
            pending >>= 8;
            bits -= 8;
        }
    }
    result
}
