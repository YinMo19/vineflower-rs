// Copyright 2000-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

//! A class-file reader. Attribute payloads and method bytecode are slices of
//! the input; interpretation of an attribute is scoped to its declared payload.

mod attributes;
mod pool;
#[cfg(test)]
mod tests;

pub use attributes::{
    Annotation, BootstrapMethod, ElementValue, InnerClass, MethodParameter, RecordComponent,
};
pub use pool::{Constant, ConstantPool, ModifiedUtf8};

#[derive(Debug, thiserror::Error)]
pub enum ClassError {
    #[error("invalid class file magic 0x{0:08x}")]
    InvalidMagic(u32),
    #[error("at byte {offset}, need {needed} bytes but only {remaining} remain")]
    UnexpectedEof {
        offset: usize,
        needed: usize,
        remaining: usize,
    },
    #[error("{context} has {remaining} trailing bytes at byte {offset}")]
    TrailingBytes {
        context: &'static str,
        offset: usize,
        remaining: usize,
    },
    #[error("constant_pool_count must include the reserved slot 0")]
    EmptyConstantPool,
    #[error("invalid constant pool tag {tag} at index {index}")]
    InvalidConstantTag { index: u16, tag: u8 },
    #[error("constant pool index {0} cannot be used because it is reserved or out of range")]
    InvalidConstantIndex(u16),
    #[error("constant pool entry {index} must be {expected}, found {actual}")]
    WrongConstantType {
        index: u16,
        expected: &'static str,
        actual: &'static str,
    },
    #[error("long or double at index {0} has no reserved slot after it")]
    MissingWideSlot(u16),
    #[error("invalid modified UTF-8 at byte {offset} of constant pool entry {index}")]
    InvalidModifiedUtf8 { index: u16, offset: usize },
    #[error("modified UTF-8 pool entry {0} contains an unpaired UTF-16 surrogate")]
    UnpairedSurrogate(u16),
    #[error("invalid Code attribute code_length {0}; must be in 1..65536")]
    InvalidCodeLength(usize),
    #[error(
        "invalid Code exception range [{start_pc}, {end_pc}) -> {handler_pc} for code_length {code_length}"
    )]
    InvalidExceptionRange {
        start_pc: u16,
        end_pc: u16,
        handler_pc: u16,
        code_length: usize,
    },
    #[error("invalid annotation element tag 0x{0:02x}")]
    InvalidElementTag(u8),
    #[error("annotation nesting exceeds the supported depth of {0}")]
    AnnotationNestingLimit(usize),
}

#[derive(Debug)]
pub struct ClassFile<'a> {
    pub minor_version: u16,
    pub major_version: u16,
    pub pool: ConstantPool<'a>,
    pub access_flags: u16,
    pub this_class: u16,
    pub super_class: u16,
    pub interfaces: Vec<u16>,
    pub fields: Vec<Member<'a>>,
    pub methods: Vec<Member<'a>>,
    pub attributes: Vec<Attribute<'a>>,
}

impl<'a> ClassFile<'a> {
    pub fn parse(bytes: &'a [u8]) -> Result<Self, ClassError> {
        let mut reader = Reader::new(bytes);
        let magic = reader.u32()?;
        if magic != 0xCAFE_BABE {
            return Err(ClassError::InvalidMagic(magic));
        }
        let minor_version = reader.u16()?;
        let major_version = reader.u16()?;
        let pool = ConstantPool::read(&mut reader, major_version <= 45 && minor_version <= 2)?;
        let access_flags = reader.u16()?;
        let this_class = reader.u16()?;
        let super_class = reader.u16()?;
        pool.expect_class(this_class)?;
        if super_class != 0 {
            pool.expect_class(super_class)?;
        }
        let interfaces = reader.table(2, |reader| {
            let index = reader.u16()?;
            pool.expect_class(index)?;
            Ok(index)
        })?;
        let fields = reader.table(8, |reader| Member::read(reader, &pool))?;
        let methods = reader.table(8, |reader| Member::read(reader, &pool))?;
        let attributes = read_attributes(&mut reader, &pool)?;
        reader.finish("class file")?;
        Ok(Self {
            minor_version,
            major_version,
            pool,
            access_flags,
            this_class,
            super_class,
            interfaces,
            fields,
            methods,
            attributes,
        })
    }
}

#[derive(Debug)]
pub struct Member<'a> {
    pub access_flags: u16,
    pub name_index: u16,
    pub descriptor_index: u16,
    pub attributes: Vec<Attribute<'a>>,
}

impl<'a> Member<'a> {
    fn read(reader: &mut Reader<'a>, pool: &ConstantPool<'a>) -> Result<Self, ClassError> {
        let access_flags = reader.u16()?;
        let name_index = reader.u16()?;
        let descriptor_index = reader.u16()?;
        pool.expect_utf8(name_index)?;
        pool.expect_utf8(descriptor_index)?;
        let attributes = read_attributes(reader, pool)?;
        Ok(Self {
            access_flags,
            name_index,
            descriptor_index,
            attributes,
        })
    }

    pub fn code(&self, pool: &ConstantPool<'a>) -> Result<Option<Code<'a>>, ClassError> {
        attributes::decode_attribute(&self.attributes, pool, "Code", |reader| {
            // Class files through 45.2 (Oak) used narrower Code header fields.
            let (max_stack, max_locals, length) = if pool.historical_code_format {
                (
                    reader.u8()?.into(),
                    reader.u8()?.into(),
                    reader.u16()?.into(),
                )
            } else {
                (reader.u16()?, reader.u16()?, reader.u32()? as usize)
            };
            if !(1..65536).contains(&length) {
                return Err(ClassError::InvalidCodeLength(length));
            }
            let bytes = reader.take(length)?;
            let exceptions = reader.table(8, |reader| {
                let start_pc = reader.u16()?;
                let end_pc = reader.u16()?;
                let handler_pc = reader.u16()?;
                let catch_type = reader.u16()?;
                if start_pc >= end_pc
                    || usize::from(end_pc) > length
                    || usize::from(handler_pc) >= length
                {
                    return Err(ClassError::InvalidExceptionRange {
                        start_pc,
                        end_pc,
                        handler_pc,
                        code_length: length,
                    });
                }
                if catch_type != 0 {
                    pool.expect_class(catch_type)?;
                }
                Ok(ExceptionHandler {
                    start_pc,
                    end_pc,
                    handler_pc,
                    catch_type,
                })
            })?;
            let attributes = read_attributes(reader, pool)?;
            Ok(Code {
                max_stack,
                max_locals,
                bytes,
                exceptions,
                attributes,
            })
        })
    }
}

#[derive(Debug)]
pub struct Code<'a> {
    pub max_stack: u16,
    pub max_locals: u16,
    pub bytes: &'a [u8],
    pub exceptions: Vec<ExceptionHandler>,
    pub attributes: Vec<Attribute<'a>>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ExceptionHandler {
    pub start_pc: u16,
    pub end_pc: u16,
    pub handler_pc: u16,
    /// A Class entry, or zero for a catch-all handler.
    pub catch_type: u16,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LocalVariable<'a> {
    pub start_pc: u16,
    pub length: u16,
    pub index: u16,
    pub name: &'a str,
    pub descriptor: &'a str,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Attribute<'a> {
    pub name_index: u16,
    pub data: &'a [u8],
}

pub fn find_attribute<'a>(
    attributes: &[Attribute<'a>],
    pool: &ConstantPool<'a>,
    name: &str,
) -> Result<Option<&'a [u8]>, ClassError> {
    for attribute in attributes {
        if pool.expect_utf8(attribute.name_index)?.as_str() == Some(name) {
            return Ok(Some(attribute.data));
        }
    }
    Ok(None)
}

fn read_attributes<'a>(
    reader: &mut Reader<'a>,
    pool: &ConstantPool<'a>,
) -> Result<Vec<Attribute<'a>>, ClassError> {
    reader.table(6, |reader| {
        let name_index = reader.u16()?;
        pool.expect_utf8(name_index)?;
        let length = reader.u32()? as usize;
        let data = reader.take(length)?;
        Ok(Attribute { name_index, data })
    })
}

struct Reader<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> Reader<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    fn require(&self, needed: usize) -> Result<(), ClassError> {
        if needed > self.bytes.len() {
            return Err(ClassError::UnexpectedEof {
                offset: self.offset,
                needed,
                remaining: self.bytes.len(),
            });
        }
        Ok(())
    }

    fn take(&mut self, length: usize) -> Result<&'a [u8], ClassError> {
        self.require(length)?;
        let (head, tail) = self.bytes.split_at(length);
        self.bytes = tail;
        self.offset += length;
        Ok(head)
    }

    fn array<const N: usize>(&mut self) -> Result<[u8; N], ClassError> {
        Ok(self.take(N)?.try_into().expect("exact-length slice"))
    }

    fn u8(&mut self) -> Result<u8, ClassError> {
        Ok(self.take(1)?[0])
    }

    fn u16(&mut self) -> Result<u16, ClassError> {
        Ok(u16::from_be_bytes(self.array()?))
    }

    fn u32(&mut self) -> Result<u32, ClassError> {
        Ok(u32::from_be_bytes(self.array()?))
    }

    fn table<T>(
        &mut self,
        entry_min_size: usize,
        entry: impl FnMut(&mut Self) -> Result<T, ClassError>,
    ) -> Result<Vec<T>, ClassError> {
        let count = self.u16()?;
        self.entries(count.into(), entry_min_size, entry)
    }

    fn entries<T>(
        &mut self,
        count: usize,
        entry_min_size: usize,
        mut entry: impl FnMut(&mut Self) -> Result<T, ClassError>,
    ) -> Result<Vec<T>, ClassError> {
        self.require(count.saturating_mul(entry_min_size))?;
        let mut result = Vec::with_capacity(count);
        for _ in 0..count {
            result.push(entry(self)?);
        }
        Ok(result)
    }

    fn finish(self, context: &'static str) -> Result<(), ClassError> {
        if self.bytes.is_empty() {
            Ok(())
        } else {
            Err(ClassError::TrailingBytes {
                context,
                offset: self.offset,
                remaining: self.bytes.len(),
            })
        }
    }
}
