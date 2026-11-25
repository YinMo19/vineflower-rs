// SPDX-License-Identifier: Apache-2.0

use crate::structs::StructMethod;
use crate::types::{CodeType, VarType};
use crate::util::text_util::is_keyword;
use rustc_hash::FxHashSet;

#[derive(Clone, Default)]
pub(crate) struct Tiny(FxHashSet<String>);

impl Tiny {
    pub(super) fn inherit(&mut self, parent: &Self) {
        self.0.extend(parent.0.iter().cloned());
    }

    pub(super) fn next(
        &mut self,
        method: &StructMethod,
        ty: Option<&VarType>,
        cleaned: &str,
    ) -> std::io::Result<Option<String>> {
        let cleaned = cleaned.rsplit('$').next().unwrap().replace("[]", "");
        self.0.insert(cleaned.clone());
        let ty = ty.ok_or_else(|| {
            std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                "Missing Tiny variable type",
            )
        })?;
        let letter = match ty.ty {
            CodeType::Bytechar | CodeType::Shortchar | CodeType::Int => Some(b'i'),
            CodeType::Long => Some(b'l'),
            CodeType::Byte => Some(b'b'),
            CodeType::Short => Some(b's'),
            CodeType::Char => Some(b'c'),
            CodeType::Float => Some(b'f'),
            CodeType::Double => Some(b'd'),
            _ => None,
        };
        let mut name = if let Some(letter) = letter {
            let mut index = usize::from(letter - b'a');
            let mut name = char::from(letter).to_string();
            while self.0.contains(&name) {
                name = letters(index);
                index += 1;
            }
            name
        } else {
            let base = match ty.ty {
                CodeType::Boolean => "bl".to_owned(),
                CodeType::Object | CodeType::Genvar => {
                    let mut base = cleaned;
                    if let Some(first) = base.chars().next()
                        && first.len_utf16() == 1
                        && first.is_uppercase()
                    {
                        // Character.toLowerCase(char) maps a single UTF-16 unit.
                        base.replace_range(
                            ..first.len_utf8(),
                            &first.to_lowercase().next().unwrap().to_string(),
                        );
                    }
                    if ty.array_dim > 0 && !base.ends_with('s') {
                        base.push('s');
                    }
                    base
                }
                _ => return Ok(None),
            };
            let mut name = base.clone();
            for index in 1.. {
                if !self.0.contains(&name) {
                    break;
                }
                name = format!("{base}{index}");
            }
            name
        };
        if is_keyword(&name, method.bytecode_version, method) {
            name.push('_');
        }
        self.0.insert(name.clone());
        Ok(Some(name))
    }
}

/// Tiny maps base-26 digits to letters, so 26 is "ba".
fn letters(mut index: usize) -> String {
    let mut bytes = Vec::new();
    loop {
        bytes.push(b'a' + (index % 26) as u8);
        index /= 26;
        if index == 0 {
            break;
        }
    }
    bytes.reverse();
    String::from_utf8(bytes).unwrap()
}
