// Copyright 2000-2017 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use super::attributes::{decode_attribute, read_annotation};
use super::{Annotation, Attribute, ClassError, ClassFile, Code, ConstantPool, Member, Reader, RecordComponent};
use crate::descriptor::{MethodDescriptor, Type};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TypeAnnotation {
    pub target: TypeTarget,
    /// From the root type to the annotated type component, in class-file order.
    pub path: Vec<TypePathStep>,
    pub annotation: Annotation,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum TypePathStep {
    ArrayElement,
    NestedType,
    WildcardBound,
    TypeArgument(u8),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Supertype {
    Superclass,
    Interface(u16),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LocalTypeRange {
    pub start_pc: u16,
    pub length: u16,
    pub index: u16,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum OffsetTarget {
    InstanceOf,
    New,
    ConstructorReference,
    MethodReference,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TypeArgumentTarget {
    Cast,
    ConstructorInvocation,
    MethodInvocation,
    ConstructorReference,
    MethodReference,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TypeTarget {
    ClassTypeParameter(u8),
    MethodTypeParameter(u8),
    Supertype(Supertype),
    ClassTypeParameterBound { parameter: u8, bound: u8 },
    MethodTypeParameterBound { parameter: u8, bound: u8 },
    Field,
    MethodReturn,
    MethodReceiver,
    MethodParameter(u8),
    Throws(u16),
    LocalVariable(Vec<LocalTypeRange>),
    ResourceVariable(Vec<LocalTypeRange>),
    Catch(u16),
    Offset { kind: OffsetTarget, offset: u16 },
    TypeArgument { kind: TypeArgumentTarget, offset: u16, argument: u8 },
}

#[derive(Clone, Copy)]
enum Owner<'a> {
    Class { has_superclass: bool, interfaces: usize },
    Field,
    Method(&'a Member<'a>),
    Code(&'a Code<'a>),
}

impl<'a> ClassFile<'a> {
    pub fn type_annotations(&self, visible: bool) -> Result<Vec<TypeAnnotation>, ClassError> {
        read(&self.attributes, &self.pool, visible, Owner::Class {
            has_superclass: self.super_class != 0,
            interfaces: self.interfaces.len(),
        })
    }
}

impl<'a> Member<'a> {
    pub fn field_type_annotations(&self, pool: &ConstantPool<'a>, visible: bool) -> Result<Vec<TypeAnnotation>, ClassError> {
        read(&self.attributes, pool, visible, Owner::Field)
    }

    pub fn method_type_annotations(&self, pool: &ConstantPool<'a>, visible: bool) -> Result<Vec<TypeAnnotation>, ClassError> {
        read(&self.attributes, pool, visible, Owner::Method(self))
    }
}

impl<'a> RecordComponent<'a> {
    pub fn type_annotations(&self, pool: &ConstantPool<'a>, visible: bool) -> Result<Vec<TypeAnnotation>, ClassError> {
        read(&self.attributes, pool, visible, Owner::Field)
    }
}

impl<'a> Code<'a> {
    pub fn type_annotations(&self, pool: &ConstantPool<'a>, visible: bool) -> Result<Vec<TypeAnnotation>, ClassError> {
        read(&self.attributes, pool, visible, Owner::Code(self))
    }
}

fn read<'a>(attributes: &[Attribute<'a>], pool: &ConstantPool<'a>, visible: bool, owner: Owner<'_>) -> Result<Vec<TypeAnnotation>, ClassError> {
    let name = if visible { "RuntimeVisibleTypeAnnotations" } else { "RuntimeInvisibleTypeAnnotations" };
    Ok(decode_attribute(attributes, pool, name, |reader| {
        let mut parameter_count = None;
        let mut throws_count = None;
        reader.table(6, |reader| {
            let target_offset = reader.offset;
            let target = read_target(reader, owner)?;
            if let Owner::Method(member) = owner {
                match target {
                    TypeTarget::MethodParameter(index) => {
                        let count = match parameter_count {
                            Some(count) => count,
                            None => {
                                let descriptor = pool.utf8(member.descriptor_index)?;
                                let descriptor = MethodDescriptor::parse(descriptor).map_err(|_| {
                                    invalid(target_offset, "invalid method descriptor for formal parameter target")
                                })?;
                                let count = descriptor.parameters.len();
                                parameter_count = Some(count);
                                count
                            }
                        };
                        if usize::from(index) >= count {
                            return Err(invalid(target_offset, "formal parameter index is out of range"));
                        }
                    }
                    TypeTarget::Throws(index) => {
                        let count = match throws_count {
                            Some(count) => count,
                            None => {
                                let count = member.exceptions(pool)?.len();
                                throws_count = Some(count);
                                count
                            }
                        };
                        if usize::from(index) >= count {
                            return Err(invalid(target_offset, "throws index is out of range"));
                        }
                    }
                    _ => {}
                }
            }
            let path_offset = reader.offset;
            let path = read_path(reader)?;
            if matches!(target, TypeTarget::ClassTypeParameter(_) | TypeTarget::MethodTypeParameter(_))
                && !path.is_empty()
            {
                return Err(invalid(path_offset, "a type parameter declaration has no type path"));
            }
            let annotation_offset = reader.offset;
            let annotation = read_annotation(reader, pool, 0)?;
            let descriptor = pool.utf8(annotation.type_index)?;
            if !matches!(Type::parse(descriptor), Ok(Type::Object(_))) {
                return Err(invalid(annotation_offset, "annotation type must be an object descriptor"));
            }
            Ok(TypeAnnotation { target, path, annotation })
        })
    })?.unwrap_or_default())
}

fn invalid(offset: usize, reason: &'static str) -> ClassError {
    ClassError::InvalidTypeAnnotation { offset, reason }
}

fn read_target(reader: &mut Reader<'_>, owner: Owner<'_>) -> Result<TypeTarget, ClassError> {
    let pos = reader.offset;
    let tag = reader.u8()?;
    let wrong_owner = || invalid(pos, "target is not permitted at this attribute location");
    Ok(match (tag, owner) {
        (0x00, Owner::Class { .. }) => TypeTarget::ClassTypeParameter(reader.u8()?),
        (0x01, Owner::Method(_)) => TypeTarget::MethodTypeParameter(reader.u8()?),
        (0x10, Owner::Class { has_superclass, interfaces }) => {
            let index = reader.u16()?;
            TypeTarget::Supertype(match index {
                u16::MAX if has_superclass => Supertype::Superclass,
                i if usize::from(i) < interfaces => Supertype::Interface(i),
                _ => return Err(invalid(pos, "supertype index is out of range")),
            })
        }
        (0x11, Owner::Class { .. }) => TypeTarget::ClassTypeParameterBound { parameter: reader.u8()?, bound: reader.u8()? },
        (0x12, Owner::Method(_)) => TypeTarget::MethodTypeParameterBound { parameter: reader.u8()?, bound: reader.u8()? },
        (0x13, Owner::Field) => TypeTarget::Field,
        (0x14, Owner::Method(_)) => TypeTarget::MethodReturn,
        (0x15, Owner::Method(member)) if member.access_flags & 0x0008 == 0 => TypeTarget::MethodReceiver,
        (0x15, Owner::Method(_)) => return Err(invalid(pos, "a static method has no receiver")),
        (0x16, Owner::Method(_)) => TypeTarget::MethodParameter(reader.u8()?),
        (0x17, Owner::Method(_)) => TypeTarget::Throws(reader.u16()?),
        (0x40 | 0x41, Owner::Code(code)) => {
            let ranges = reader.table(6, |reader| {
                let pos = reader.offset;
                let start_pc = reader.u16()?;
                let length = reader.u16()?;
                let index = reader.u16()?;
                let start = usize::from(start_pc);
                if start >= code.bytes.len() || start + usize::from(length) > code.bytes.len() {
                    return Err(invalid(pos, "local variable range is outside Code"));
                }
                if index >= code.max_locals {
                    return Err(invalid(pos, "local variable index is outside max_locals"));
                }
                Ok(LocalTypeRange { start_pc, length, index })
            })?;
            if tag == 0x40 { TypeTarget::LocalVariable(ranges) } else { TypeTarget::ResourceVariable(ranges) }
        }
        (0x42, Owner::Code(code)) => {
            let index = reader.u16()?;
            if usize::from(index) >= code.exceptions.len() {
                return Err(invalid(pos, "catch index is outside the Code exception table"));
            }
            TypeTarget::Catch(index)
        }
        (0x43..=0x46, Owner::Code(code)) => TypeTarget::Offset {
            kind: match tag {
                0x43 => OffsetTarget::InstanceOf,
                0x44 => OffsetTarget::New,
                0x45 => OffsetTarget::ConstructorReference,
                _ => OffsetTarget::MethodReference,
            },
            offset: read_code_offset(reader, code)?,
        },
        (0x47..=0x4b, Owner::Code(code)) => TypeTarget::TypeArgument {
            kind: match tag {
                0x47 => TypeArgumentTarget::Cast,
                0x48 => TypeArgumentTarget::ConstructorInvocation,
                0x49 => TypeArgumentTarget::MethodInvocation,
                0x4a => TypeArgumentTarget::ConstructorReference,
                _ => TypeArgumentTarget::MethodReference,
            },
            offset: read_code_offset(reader, code)?,
            argument: reader.u8()?,
        },
        (0x00..=0x01 | 0x10..=0x17 | 0x40..=0x4b, _) => return Err(wrong_owner()),
        _ => return Err(invalid(pos, "unknown target type")),
    })
}

fn read_code_offset(reader: &mut Reader<'_>, code: &Code<'_>) -> Result<u16, ClassError> {
    let pos = reader.offset;
    let offset = reader.u16()?;
    if usize::from(offset) >= code.bytes.len() {
        return Err(invalid(pos, "instruction offset is outside Code"));
    }
    Ok(offset)
}

fn read_path(reader: &mut Reader<'_>) -> Result<Vec<TypePathStep>, ClassError> {
    let length = usize::from(reader.u8()?);
    reader.entries(length, 2, |reader| {
        let pos = reader.offset;
        Ok(match (reader.u8()?, reader.u8()?) {
            (0, 0) => TypePathStep::ArrayElement,
            (1, 0) => TypePathStep::NestedType,
            (2, 0) => TypePathStep::WildcardBound,
            (3, index) => TypePathStep::TypeArgument(index),
            (0..=2, _) => return Err(invalid(pos, "non-argument path step has a nonzero argument index")),
            _ => return Err(invalid(pos, "unknown path step kind")),
        })
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn pool(entries: &[&str]) -> Vec<u8> {
        let mut bytes = ((entries.len() + 1) as u16).to_be_bytes().to_vec();
        for entry in entries {
            bytes.push(1); // CONSTANT_Utf8
            bytes.extend((entry.len() as u16).to_be_bytes());
            bytes.extend(entry.as_bytes());
        }
        bytes
    }

    #[test]
    fn record_component_uses_field_target_and_keeps_visibility_separate() {
        // TestRecordAnno's `@TA @RC int x`: TA is a type annotation and RC is
        // a declaration annotation, both stored as runtime-invisible by javac.
        let bytes = pool(&["RuntimeInvisibleTypeAnnotations", "Lpkg/TA;", "RuntimeInvisibleAnnotations", "Lpkg/RC;", "x", "I"]);
        let pool = ConstantPool::read(&mut Reader::new(&bytes), false).unwrap();
        let component = RecordComponent {
            name_index: 5,
            descriptor_index: 6,
            attributes: vec![
                Attribute { name_index: 1, data: &[0, 1, 0x13, 0, 0, 2, 0, 0] },
                Attribute { name_index: 3, data: &[0, 1, 0, 4, 0, 0] },
            ],
        };
        assert!(component.type_annotations(&pool, true).unwrap().is_empty());
        let decoded = component.type_annotations(&pool, false).unwrap();
        assert_eq!(decoded.len(), 1);
        assert_eq!(decoded[0].target, TypeTarget::Field);
        assert!(decoded[0].path.is_empty());
        assert_eq!(pool.utf8(decoded[0].annotation.type_index).unwrap(), "Lpkg/TA;");
    }

    #[test]
    fn preserves_local_ranges_and_expression_argument_offsets() {
        let bytes = pool(&["RuntimeVisibleTypeAnnotations", "Lpkg/A;"]);
        let pool = ConstantPool::read(&mut Reader::new(&bytes), false).unwrap();
        let code = Code {
            max_stack: 0,
            max_locals: 3,
            bytes: &[0; 8],
            exceptions: vec![],
            attributes: vec![Attribute {
                name_index: 1,
                data: &[
                    0, 2, // Annotation count.
                    0x41, 0, 2, 0, 1, 0, 2, 0, 2, 0, 4, 0, 4, 0, 2,
                    2, 0, 0, 3, 200, 0, 2, 0, 0,
                    0x4b, 0, 6, 129, 0, 0, 2, 0, 0,
                ],
            }],
        };
        let annotations = code.type_annotations(&pool, true).unwrap();
        assert_eq!(annotations[0].target, TypeTarget::ResourceVariable(vec![
            LocalTypeRange { start_pc: 1, length: 2, index: 2 },
            LocalTypeRange { start_pc: 4, length: 4, index: 2 },
        ]));
        assert_eq!(annotations[0].path, [TypePathStep::ArrayElement, TypePathStep::TypeArgument(200)]);
        assert_eq!(annotations[1].target, TypeTarget::TypeArgument {
            kind: TypeArgumentTarget::MethodReference, offset: 6, argument: 129,
        });
    }

    #[test]
    fn rejects_wrong_owner_bad_ranges_and_reserved_tags() {
        let code = Code {
            max_stack: 0, max_locals: 1, bytes: &[0; 5], exceptions: vec![], attributes: vec![],
        };
        for (owner, data, reason) in [
            (Owner::Field, &[0x14][..], "target is not permitted at this attribute location"),
            (Owner::Field, &[0x18], "unknown target type"),
            (Owner::Code(&code), &[0x42, 0, 0], "catch index is outside the Code exception table"),
            (Owner::Code(&code), &[0x43, 0, 5], "instruction offset is outside Code"),
            (Owner::Code(&code), &[0x40, 0, 1, 0, 4, 0, 2, 0, 0], "local variable range is outside Code"),
            (Owner::Code(&code), &[0x40, 0, 1, 0, 4, 0, 1, 0, 1], "local variable index is outside max_locals"),
        ] {
            assert!(matches!(
                read_target(&mut Reader::new(data), owner),
                Err(ClassError::InvalidTypeAnnotation { reason: actual, .. }) if actual == reason
            ));
        }
        for data in [[1, 0, 1], [1, 1, 1], [1, 2, 1], [1, 4, 0]] {
            assert!(matches!(read_path(&mut Reader::new(&data)), Err(ClassError::InvalidTypeAnnotation { offset: 1, .. })));
        }
    }

    #[test]
    fn validates_annotation_pool_reference_and_descriptor() {
        let bytes = pool(&["RuntimeVisibleTypeAnnotations", "I"]);
        let pool = ConstantPool::read(&mut Reader::new(&bytes), false).unwrap();
        let attributes = [Attribute { name_index: 1, data: &[0, 1, 0x13, 0, 0, 2, 0, 0] }];
        assert!(matches!(
            read(&attributes, &pool, true, Owner::Field),
            Err(ClassError::InvalidTypeAnnotation { offset: 4, .. })
        ));
        let attributes = [Attribute { name_index: 1, data: &[0, 1, 0x13, 0, 0, 3, 0, 0] }];
        assert!(matches!(
            read(&attributes, &pool, true, Owner::Field),
            Err(ClassError::InvalidConstantIndex(3))
        ));
    }

    #[test]
    fn rejects_method_targets_without_a_matching_declaration() {
        let bytes = pool(&["RuntimeVisibleTypeAnnotations", "Lpkg/A;", "m", "(I)V"]);
        let pool = ConstantPool::read(&mut Reader::new(&bytes), false).unwrap();
        for (data, reason) in [
            (&[0, 1, 0x15, 0, 0, 2, 0, 0][..], "a static method has no receiver"),
            (&[0, 1, 0x16, 1, 0, 0, 2, 0, 0], "formal parameter index is out of range"),
            (&[0, 1, 0x17, 0, 0, 0, 0, 2, 0, 0], "throws index is out of range"),
            (&[0, 1, 0x01, 0, 1, 0, 0, 0, 2, 0, 0], "a type parameter declaration has no type path"),
        ] {
            let member = Member {
                access_flags: 0x0008,
                name_index: 3,
                descriptor_index: 4,
                attributes: vec![Attribute { name_index: 1, data }],
            };
            assert!(matches!(
                member.method_type_annotations(&pool, true),
                Err(ClassError::InvalidTypeAnnotation { reason: actual, .. }) if actual == reason
            ));
        }
    }
}
