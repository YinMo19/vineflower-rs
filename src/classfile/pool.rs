// Copyright 2000-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use std::borrow::Cow;

use super::{ClassError, Reader};

/// A JVM UTF-8 constant. Java strings are sequences of UTF-16 code units;
/// unpaired surrogates are valid data, but cannot be represented by a Rust str.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ModifiedUtf8<'a>(ModifiedUtf8Text<'a>);

#[derive(Clone, Debug, Eq, PartialEq)]
enum ModifiedUtf8Text<'a> {
    Unicode(Cow<'a, str>),
    UnpairedSurrogates(Vec<u16>),
}

impl<'a> ModifiedUtf8<'a> {
    fn parse(bytes: &'a [u8], index: u16) -> Result<Self, ClassError> {
        // cesu8 accepts all standard UTF-8 as a fast path. The JVM encoding
        // does not allow literal NUL or four-byte UTF-8 sequences.
        if let Some(offset) = bytes.iter().position(|byte| *byte == 0 || *byte >= 0xf0) {
            return Err(ClassError::InvalidModifiedUtf8 { index, offset });
        }
        if let Ok(text) = cesu8::from_java_cesu8(bytes) {
            return Ok(Self(ModifiedUtf8Text::Unicode(text)));
        }

        // For a value which cannot become a str, decode code units instead.
        // Validate entire sequences, including overlong encodings, in this path.
        let mut units = Vec::new();
        let mut remaining = bytes;
        while !remaining.is_empty() {
            let (unit, rest) = match remaining {
                [byte @ 0x01..=0x7f, rest @ ..] => (u16::from(*byte), rest),
                [0xc0, 0x80, rest @ ..] => (0, rest),
                [a @ 0xc2..=0xdf, b @ 0x80..=0xbf, rest @ ..] => {
                    ((u16::from(a & 0x1f) << 6) | u16::from(b & 0x3f), rest)
                }
                [a @ 0xe0..=0xef, b @ 0x80..=0xbf, c @ 0x80..=0xbf, rest @ ..]
                    if *a != 0xe0 || *b >= 0xa0 =>
                {
                    (
                        (u16::from(a & 0x0f) << 12)
                            | (u16::from(b & 0x3f) << 6)
                            | u16::from(c & 0x3f),
                        rest,
                    )
                }
                _ => {
                    return Err(ClassError::InvalidModifiedUtf8 {
                        index,
                        offset: bytes.len() - remaining.len(),
                    });
                }
            };
            units.push(unit);
            remaining = rest;
        }
        Ok(Self(ModifiedUtf8Text::UnpairedSurrogates(units)))
    }

    pub fn as_str(&self) -> Option<&str> {
        match &self.0 {
            ModifiedUtf8Text::Unicode(text) => Some(text),
            ModifiedUtf8Text::UnpairedSurrogates(_) => None,
        }
    }

    pub fn utf16(&self) -> Cow<'_, [u16]> {
        match &self.0 {
            ModifiedUtf8Text::Unicode(text) => Cow::Owned(text.encode_utf16().collect()),
            ModifiedUtf8Text::UnpairedSurrogates(units) => Cow::Borrowed(units),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Constant<'a> {
    Utf8(ModifiedUtf8<'a>),
    Integer(i32),
    Float(f32),
    Long(i64),
    Double(f64),
    Class(u16),
    String(u16),
    Fieldref {
        class_index: u16,
        name_and_type_index: u16,
    },
    Methodref {
        class_index: u16,
        name_and_type_index: u16,
    },
    InterfaceMethodref {
        class_index: u16,
        name_and_type_index: u16,
    },
    NameAndType {
        name_index: u16,
        descriptor_index: u16,
    },
    MethodHandle {
        reference_kind: u8,
        reference_index: u16,
    },
    MethodType(u16),
    Dynamic {
        bootstrap_index: u16,
        name_and_type_index: u16,
    },
    InvokeDynamic {
        bootstrap_index: u16,
        name_and_type_index: u16,
    },
    Module(u16),
    Package(u16),
}

impl Constant<'_> {
    pub(super) fn kind(&self) -> &'static str {
        match self {
            Self::Utf8(_) => "Utf8",
            Self::Integer(_) => "Integer",
            Self::Float(_) => "Float",
            Self::Long(_) => "Long",
            Self::Double(_) => "Double",
            Self::Class(_) => "Class",
            Self::String(_) => "String",
            Self::Fieldref { .. } => "Fieldref",
            Self::Methodref { .. } => "Methodref",
            Self::InterfaceMethodref { .. } => "InterfaceMethodref",
            Self::NameAndType { .. } => "NameAndType",
            Self::MethodHandle { .. } => "MethodHandle",
            Self::MethodType(_) => "MethodType",
            Self::Dynamic { .. } => "Dynamic",
            Self::InvokeDynamic { .. } => "InvokeDynamic",
            Self::Module(_) => "Module",
            Self::Package(_) => "Package",
        }
    }
}

#[derive(Debug)]
pub struct ConstantPool<'a> {
    entries: Vec<Option<Constant<'a>>>,
    pub(super) historical_code_format: bool,
}

impl<'a> ConstantPool<'a> {
    pub(super) fn read(
        reader: &mut Reader<'a>,
        historical_code_format: bool,
    ) -> Result<Self, ClassError> {
        let count = reader.u16()?;
        if count == 0 {
            return Err(ClassError::EmptyConstantPool);
        }
        // A one-slot constant requires at least 3 bytes (empty Utf8); a
        // two-slot constant needs 9 bytes. Bound allocation before parsing.
        reader.require(usize::from(count - 1) * 3)?;
        let mut entries = Vec::with_capacity(count.into());
        entries.push(None);
        let mut index = 1;
        while index < count {
            let tag = reader.u8()?;
            let item = match tag {
                1 => {
                    let length = reader.u16()?;
                    Constant::Utf8(ModifiedUtf8::parse(reader.take(length.into())?, index)?)
                }
                3 => Constant::Integer(i32::from_be_bytes(reader.array()?)),
                4 => Constant::Float(f32::from_bits(reader.u32()?)),
                5 => Constant::Long(i64::from_be_bytes(reader.array()?)),
                6 => Constant::Double(f64::from_bits(u64::from_be_bytes(reader.array()?))),
                7 => Constant::Class(reader.u16()?),
                8 => Constant::String(reader.u16()?),
                9 => Constant::Fieldref {
                    class_index: reader.u16()?,
                    name_and_type_index: reader.u16()?,
                },
                10 => Constant::Methodref {
                    class_index: reader.u16()?,
                    name_and_type_index: reader.u16()?,
                },
                11 => Constant::InterfaceMethodref {
                    class_index: reader.u16()?,
                    name_and_type_index: reader.u16()?,
                },
                12 => Constant::NameAndType {
                    name_index: reader.u16()?,
                    descriptor_index: reader.u16()?,
                },
                15 => Constant::MethodHandle {
                    reference_kind: reader.u8()?,
                    reference_index: reader.u16()?,
                },
                16 => Constant::MethodType(reader.u16()?),
                17 => Constant::Dynamic {
                    bootstrap_index: reader.u16()?,
                    name_and_type_index: reader.u16()?,
                },
                18 => Constant::InvokeDynamic {
                    bootstrap_index: reader.u16()?,
                    name_and_type_index: reader.u16()?,
                },
                19 => Constant::Module(reader.u16()?),
                20 => Constant::Package(reader.u16()?),
                _ => return Err(ClassError::InvalidConstantTag { index, tag }),
            };
            let wide = matches!(item, Constant::Long(_) | Constant::Double(_));
            entries.push(Some(item));
            if wide {
                if index + 1 == count {
                    return Err(ClassError::MissingWideSlot(index));
                }
                entries.push(None);
                index += 1;
            }
            index += 1;
        }
        Ok(Self {
            entries,
            historical_code_format,
        })
    }

    pub fn get(&self, index: u16) -> Result<&Constant<'a>, ClassError> {
        self.entries
            .get(usize::from(index))
            .and_then(Option::as_ref)
            .ok_or(ClassError::InvalidConstantIndex(index))
    }

    pub fn iter(&self) -> impl Iterator<Item = &Constant<'a>> {
        self.entries.iter().flatten()
    }

    /// Decode as Unicode text without replacing any unpaired surrogates.
    /// Use [`Self::utf16`] for Java string literal contents.
    pub fn utf8(&self, index: u16) -> Result<&str, ClassError> {
        self.expect_utf8(index)?
            .as_str()
            .ok_or(ClassError::UnpairedSurrogate(index))
    }

    pub fn utf16(&self, index: u16) -> Result<Cow<'_, [u16]>, ClassError> {
        Ok(self.expect_utf8(index)?.utf16())
    }

    pub fn class_name(&self, index: u16) -> Result<&str, ClassError> {
        self.utf8(self.class_name_index(index)?)
    }

    pub fn name_and_type(&self, index: u16) -> Result<(&str, &str), ClassError> {
        match *self.get(index)? {
            Constant::NameAndType {
                name_index,
                descriptor_index,
            } => Ok((self.utf8(name_index)?, self.utf8(descriptor_index)?)),
            ref other => Err(wrong_type(index, "NameAndType", other)),
        }
    }

    pub fn member_ref(&self, index: u16) -> Result<(&str, &str, &str), ClassError> {
        match *self.get(index)? {
            Constant::Fieldref {
                class_index,
                name_and_type_index,
            }
            | Constant::Methodref {
                class_index,
                name_and_type_index,
            }
            | Constant::InterfaceMethodref {
                class_index,
                name_and_type_index,
            } => {
                let owner = self.class_name(class_index)?;
                let (name, descriptor) = self.name_and_type(name_and_type_index)?;
                Ok((owner, name, descriptor))
            }
            ref other => Err(wrong_type(
                index,
                "Fieldref, Methodref, or InterfaceMethodref",
                other,
            )),
        }
    }

    fn class_name_index(&self, index: u16) -> Result<u16, ClassError> {
        match *self.get(index)? {
            Constant::Class(name) => Ok(name),
            ref other => Err(wrong_type(index, "Class", other)),
        }
    }

    pub(super) fn expect_class(&self, index: u16) -> Result<(), ClassError> {
        self.expect_utf8(self.class_name_index(index)?)?;
        Ok(())
    }

    pub(super) fn expect_utf8(&self, index: u16) -> Result<&ModifiedUtf8<'a>, ClassError> {
        match self.get(index)? {
            Constant::Utf8(value) => Ok(value),
            other => Err(wrong_type(index, "Utf8", other)),
        }
    }
}

pub(super) fn wrong_type(index: u16, expected: &'static str, actual: &Constant<'_>) -> ClassError {
    ClassError::WrongConstantType {
        index,
        expected,
        actual: actual.kind(),
    }
}
