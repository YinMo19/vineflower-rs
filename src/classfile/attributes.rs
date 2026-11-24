// Copyright 2000-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use super::pool::wrong_type;
use super::{
    Attribute, ClassError, ClassFile, Code, Constant, ConstantPool, LocalVariable, Member, Reader,
    find_attribute, read_attributes,
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BootstrapMethod {
    pub method_ref: u16,
    pub arguments: Vec<u16>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct InnerClass {
    pub inner_class: u16,
    /// A Class index, or zero if the inner class is not a member class.
    pub outer_class: u16,
    /// A Utf8 index, or zero if the class is anonymous.
    pub inner_name: u16,
    pub access_flags: u16,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RecordComponent<'a> {
    pub name_index: u16,
    pub descriptor_index: u16,
    pub attributes: Vec<Attribute<'a>>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct MethodParameter {
    /// A Utf8 index, or zero when the parameter has no name.
    pub name_index: u16,
    pub access_flags: u16,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Annotation {
    pub type_index: u16,
    /// Pairs of a Utf8 name index and its value, in class-file order.
    pub elements: Vec<(u16, ElementValue)>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ElementValue {
    /// The element tag is preserved (e.g. 'Z' and 'I' both use Integer entries).
    Constant {
        tag: u8,
        index: u16,
    },
    Enum {
        type_name_index: u16,
        const_name_index: u16,
    },
    Class(u16),
    Annotation(Box<Annotation>),
    Array(Vec<ElementValue>),
}

impl<'a> ClassFile<'a> {
    pub fn bootstrap_methods(&self) -> Result<Vec<BootstrapMethod>, ClassError> {
        let pool = &self.pool;
        Ok(
            decode_attribute(&self.attributes, pool, "BootstrapMethods", |reader| {
                reader.table(4, |reader| {
                    let method_ref = reader.u16()?;
                    let method = pool.get(method_ref)?;
                    if !matches!(method, Constant::MethodHandle { .. }) {
                        return Err(wrong_type(method_ref, "MethodHandle", method));
                    }
                    let arguments = reader.table(2, |reader| {
                        let index = reader.u16()?;
                        let argument = pool.get(index)?;
                        if !matches!(
                            argument,
                            Constant::Integer(_)
                                | Constant::Float(_)
                                | Constant::Long(_)
                                | Constant::Double(_)
                                | Constant::String(_)
                                | Constant::Class(_)
                                | Constant::MethodHandle { .. }
                                | Constant::MethodType(_)
                                | Constant::Dynamic { .. }
                        ) {
                            return Err(wrong_type(
                                index,
                                "a loadable bootstrap argument",
                                argument,
                            ));
                        }
                        Ok(index)
                    })?;
                    Ok(BootstrapMethod {
                        method_ref,
                        arguments,
                    })
                })
            })?
            .unwrap_or_default(),
        )
    }

    pub fn signature(&self) -> Result<Option<&str>, ClassError> {
        signature(&self.attributes, &self.pool)
    }

    pub fn inner_classes(&self) -> Result<Vec<InnerClass>, ClassError> {
        let pool = &self.pool;
        Ok(
            decode_attribute(&self.attributes, pool, "InnerClasses", |reader| {
                reader.table(8, |reader| {
                    let inner_class = reader.u16()?;
                    let outer_class = reader.u16()?;
                    let inner_name = reader.u16()?;
                    let access_flags = reader.u16()?;
                    pool.expect_class(inner_class)?;
                    if outer_class != 0 {
                        pool.expect_class(outer_class)?;
                    }
                    if inner_name != 0 {
                        pool.expect_utf8(inner_name)?;
                    }
                    Ok(InnerClass {
                        inner_class,
                        outer_class,
                        inner_name,
                        access_flags,
                    })
                })
            })?
            .unwrap_or_default(),
        )
    }

    pub fn record_components(&self) -> Result<Option<Vec<RecordComponent<'a>>>, ClassError> {
        let pool = &self.pool;
        decode_attribute(&self.attributes, pool, "Record", |reader| {
            reader.table(6, |reader| {
                let name_index = reader.u16()?;
                let descriptor_index = reader.u16()?;
                pool.expect_utf8(name_index)?;
                pool.expect_utf8(descriptor_index)?;
                let attributes = read_attributes(reader, pool)?;
                Ok(RecordComponent {
                    name_index,
                    descriptor_index,
                    attributes,
                })
            })
        })
    }

    pub fn permitted_subclasses(&self) -> Result<Vec<u16>, ClassError> {
        class_index_table(&self.attributes, &self.pool, "PermittedSubclasses")
    }

    pub fn annotations(&self, visible: bool) -> Result<Vec<Annotation>, ClassError> {
        annotations(&self.attributes, &self.pool, visible)
    }
}

impl<'a> Member<'a> {
    pub fn signature<'p>(&self, pool: &'p ConstantPool<'a>) -> Result<Option<&'p str>, ClassError> {
        signature(&self.attributes, pool)
    }

    pub fn exceptions(&self, pool: &ConstantPool<'a>) -> Result<Vec<u16>, ClassError> {
        class_index_table(&self.attributes, pool, "Exceptions")
    }

    pub fn method_parameters(
        &self,
        pool: &ConstantPool<'a>,
    ) -> Result<Vec<MethodParameter>, ClassError> {
        Ok(
            decode_attribute(&self.attributes, pool, "MethodParameters", |reader| {
                let count = reader.u8()?;
                reader.entries(count.into(), 4, |reader| {
                    let name_index = reader.u16()?;
                    if name_index != 0 {
                        pool.expect_utf8(name_index)?;
                    }
                    let access_flags = reader.u16()?;
                    Ok(MethodParameter {
                        name_index,
                        access_flags,
                    })
                })
            })?
            .unwrap_or_default(),
        )
    }

    pub fn annotations(
        &self,
        pool: &ConstantPool<'a>,
        visible: bool,
    ) -> Result<Vec<Annotation>, ClassError> {
        annotations(&self.attributes, pool, visible)
    }

    pub fn parameter_annotations(
        &self,
        pool: &ConstantPool<'a>,
        visible: bool,
    ) -> Result<Vec<Vec<Annotation>>, ClassError> {
        let name = if visible {
            "RuntimeVisibleParameterAnnotations"
        } else {
            "RuntimeInvisibleParameterAnnotations"
        };
        Ok(decode_attribute(&self.attributes, pool, name, |reader| {
            let count = reader.u8()?;
            reader.entries(count.into(), 2, |reader| parse_annotations(reader, pool))
        })?
        .unwrap_or_default())
    }

    pub fn annotation_default(
        &self,
        pool: &ConstantPool<'a>,
    ) -> Result<Option<ElementValue>, ClassError> {
        decode_attribute(&self.attributes, pool, "AnnotationDefault", |reader| {
            read_element(reader, pool, 0)
        })
    }
}

impl<'a> RecordComponent<'a> {
    pub fn signature<'p>(&self, pool: &'p ConstantPool<'a>) -> Result<Option<&'p str>, ClassError> {
        signature(&self.attributes, pool)
    }

    pub fn annotations(
        &self,
        pool: &ConstantPool<'a>,
        visible: bool,
    ) -> Result<Vec<Annotation>, ClassError> {
        annotations(&self.attributes, pool, visible)
    }
}

impl<'a> Code<'a> {
    pub fn local_variables<'p>(
        &self,
        pool: &'p ConstantPool<'a>,
    ) -> Result<Vec<LocalVariable<'p>>, ClassError> {
        decode_repeated_tables(&self.attributes, pool, "LocalVariableTable", 10, |reader| {
            let start_pc = reader.u16()?;
            let length = reader.u16()?;
            let name = pool.utf8(reader.u16()?)?;
            let descriptor = pool.utf8(reader.u16()?)?;
            let index = reader.u16()?;
            Ok(LocalVariable {
                start_pc,
                length,
                index,
                name,
                descriptor,
            })
        })
    }

    pub fn line_numbers(&self, pool: &ConstantPool<'a>) -> Result<Vec<(u16, u16)>, ClassError> {
        decode_repeated_tables(&self.attributes, pool, "LineNumberTable", 4, |reader| {
            Ok((reader.u16()?, reader.u16()?))
        })
    }
}

fn signature<'p>(
    attributes: &[Attribute<'_>],
    pool: &'p ConstantPool<'_>,
) -> Result<Option<&'p str>, ClassError> {
    decode_attribute(attributes, pool, "Signature", |reader| {
        pool.utf8(reader.u16()?)
    })
}

fn class_index_table(
    attributes: &[Attribute<'_>],
    pool: &ConstantPool<'_>,
    name: &'static str,
) -> Result<Vec<u16>, ClassError> {
    Ok(decode_attribute(attributes, pool, name, |reader| {
        reader.table(2, |reader| {
            let index = reader.u16()?;
            pool.expect_class(index)?;
            Ok(index)
        })
    })?
    .unwrap_or_default())
}

fn annotations(
    attributes: &[Attribute<'_>],
    pool: &ConstantPool<'_>,
    visible: bool,
) -> Result<Vec<Annotation>, ClassError> {
    let name = if visible {
        "RuntimeVisibleAnnotations"
    } else {
        "RuntimeInvisibleAnnotations"
    };
    Ok(decode_attribute(attributes, pool, name, |reader| {
        parse_annotations(reader, pool)
    })?
    .unwrap_or_default())
}

fn parse_annotations(
    reader: &mut Reader<'_>,
    pool: &ConstantPool<'_>,
) -> Result<Vec<Annotation>, ClassError> {
    reader.table(4, |reader| read_annotation(reader, pool, 0))
}

fn read_annotation(
    reader: &mut Reader<'_>,
    pool: &ConstantPool<'_>,
    depth: usize,
) -> Result<Annotation, ClassError> {
    let type_index = reader.u16()?;
    pool.expect_utf8(type_index)?;
    let elements = reader.table(5, |reader| {
        let name = reader.u16()?;
        pool.expect_utf8(name)?;
        Ok((name, read_element(reader, pool, depth)?))
    })?;
    Ok(Annotation {
        type_index,
        elements,
    })
}

fn read_element(
    reader: &mut Reader<'_>,
    pool: &ConstantPool<'_>,
    depth: usize,
) -> Result<ElementValue, ClassError> {
    // Protect both the parser and consumers of the recursive annotation tree.
    const MAX_NESTING: usize = 128;
    if depth >= MAX_NESTING {
        return Err(ClassError::AnnotationNestingLimit(MAX_NESTING));
    }
    match reader.u8()? {
        b'e' => {
            let type_name_index = reader.u16()?;
            let const_name_index = reader.u16()?;
            pool.expect_utf8(type_name_index)?;
            pool.expect_utf8(const_name_index)?;
            Ok(ElementValue::Enum {
                type_name_index,
                const_name_index,
            })
        }
        b'c' => {
            let index = reader.u16()?;
            pool.expect_utf8(index)?;
            Ok(ElementValue::Class(index))
        }
        b'@' => Ok(ElementValue::Annotation(Box::new(read_annotation(
            reader,
            pool,
            depth + 1,
        )?))),
        b'[' => {
            Ok(ElementValue::Array(reader.table(3, |reader| {
                read_element(reader, pool, depth + 1)
            })?))
        }
        tag => {
            let expected = match tag {
                b'B' | b'C' | b'I' | b'S' | b'Z' => "Integer",
                b'D' => "Double",
                b'F' => "Float",
                b'J' => "Long",
                b's' => "Utf8",
                _ => return Err(ClassError::InvalidElementTag(tag)),
            };
            let index = reader.u16()?;
            let item = pool.get(index)?;
            if item.kind() != expected {
                return Err(wrong_type(index, expected, item));
            }
            Ok(ElementValue::Constant { tag, index })
        }
    }
}

pub(super) fn decode_attribute<'a, T>(
    attributes: &[Attribute<'a>],
    pool: &ConstantPool<'a>,
    name: &'static str,
    read: impl FnOnce(&mut Reader<'a>) -> Result<T, ClassError>,
) -> Result<Option<T>, ClassError> {
    let Some(bytes) = find_attribute(attributes, pool, name)? else {
        return Ok(None);
    };
    let mut reader = Reader::new(bytes);
    let result = read(&mut reader)?;
    reader.finish(name)?;
    Ok(Some(result))
}

fn decode_repeated_tables<'a, T>(
    attributes: &[Attribute<'a>],
    pool: &ConstantPool<'_>,
    name: &'static str,
    entry_size: usize,
    mut entry: impl FnMut(&mut Reader<'a>) -> Result<T, ClassError>,
) -> Result<Vec<T>, ClassError> {
    let mut entries = Vec::new();
    for attribute in attributes {
        if pool.expect_utf8(attribute.name_index)?.as_str() != Some(name) {
            continue;
        }
        let mut reader = Reader::new(attribute.data);
        let count = usize::from(reader.u16()?);
        reader.require(count * entry_size)?;
        entries.reserve(count);
        for _ in 0..count {
            entries.push(entry(&mut reader)?);
        }
        reader.finish(name)?;
    }
    Ok(entries)
}
