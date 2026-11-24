// Based on Vineflower annotation attributes and AnnotationExprent (Apache-2.0).
use std::borrow::Cow;

use super::{DecompileError, Document, Token, TokenKind, Writer, parse, symbols};
use crate::{
    classfile::{Annotation, Attribute, ElementValue, Member, find_attribute},
    descriptor::{Primitive, Type},
    lift::{constant_literal_with_options, string_literal},
};

impl<'a> Writer<'a, '_> {
    pub(super) fn class_annotations(&mut self, depth: usize) -> Result<(), DecompileError> {
        for visible in [true, false] {
            for annotation in self.class.annotations(visible)? {
                self.write_annotation(depth, &annotation)?;
            }
        }
        Ok(())
    }

    pub(super) fn class_deprecation(&mut self, depth: usize) -> Result<(), DecompileError> {
        if find_attribute(&self.class.attributes, &self.class.pool, "Deprecated")?.is_none() {
            return Ok(());
        }
        let visible = self.class.annotations(true)?;
        let invisible = self.class.annotations(false)?;
        self.deprecation_comment(depth, visible.iter().chain(&invisible))
    }

    pub(super) fn member_deprecation(
        &mut self,
        depth: usize,
        attributes: &[Attribute<'a>],
        annotations: &[Annotation],
    ) -> Result<(), DecompileError> {
        if find_attribute(attributes, &self.class.pool, "Deprecated")?.is_some() {
            self.deprecation_comment(depth, annotations)?;
        }
        Ok(())
    }

    fn deprecation_comment<'b>(
        &mut self,
        depth: usize,
        annotations: impl IntoIterator<Item = &'b Annotation>,
    ) -> Result<(), DecompileError> {
        for annotation in annotations {
            if self.class.pool.utf8(annotation.type_index)? == "Ljava/lang/Deprecated;" {
                return Ok(());
            }
        }
        self.line(depth, "/** @deprecated */");
        Ok(())
    }

    pub(super) fn annotations_of(
        &self,
        member: &Member<'a>,
    ) -> Result<Vec<Annotation>, DecompileError> {
        let mut result = member.annotations(&self.class.pool, true)?;
        result.extend(member.annotations(&self.class.pool, false)?);
        Ok(result)
    }

    pub(super) fn write_annotation(
        &mut self,
        depth: usize,
        annotation: &Annotation,
    ) -> Result<(), DecompileError> {
        let doc = self.annotation_document(annotation, Some(self.depth + depth))?;
        self.document_line(depth, &doc);
        Ok(())
    }

    pub(super) fn annotation_document(
        &self,
        annotation: &Annotation,
        depth: Option<usize>,
    ) -> Result<Document, DecompileError> {
        let pool = &self.class.pool;
        let ty = parse(pool.utf8(annotation.type_index)?, Type::parse)?;
        let Type::Object(owner) = ty else {
            return Err(DecompileError::InvalidAttribute("annotation type"));
        };
        let name = self.names.render(&owner);
        let mut elements = Vec::with_capacity(annotation.elements.len());
        for (member, value) in &annotation.elements {
            let member = pool.utf8(*member)?;
            let mut doc = Document::new();
            if annotation.elements.len() != 1 || member != "value" {
                if self.options.dump_text_tokens
                    && let Some(descriptor) = self.annotation_member_type(&owner, member, value)?
                {
                    doc.token(
                        member,
                        Token {
                            declaration: false,
                            kind: TokenKind::Method {
                                owner: owner.clone(),
                                name: member.into(),
                                descriptor: descriptor.into_owned(),
                            },
                        },
                    );
                } else {
                    doc.push_str(member);
                }
                doc.push_str(" = ");
            }
            if let ElementValue::Array(values) = value
                && let [only] = values.as_slice()
                && !matches!(only, ElementValue::Array(_))
            {
                doc.append(self.annotation_value(only)?);
            } else {
                doc.append(self.annotation_value(value)?);
            }
            elements.push(doc);
        }
        let mut doc = match depth {
            Some(depth) => Document::annotation(depth, &name, elements),
            None => Document::inline_annotation(&name, elements),
        };
        if self.options.dump_text_tokens {
            symbols::class_ranges(&mut doc, 1, &name, &owner);
        }
        Ok(doc)
    }

    pub(super) fn annotation_value(
        &self,
        value: &ElementValue,
    ) -> Result<Document, DecompileError> {
        let pool = &self.class.pool;
        match value {
            ElementValue::Constant { tag: b's', index } => {
                Ok(string_literal(&pool.utf16(*index)?, self.options.ascii_strings).into())
            }
            ElementValue::Constant { tag, index } => {
                let primitive = match tag {
                    b'B' => Primitive::Byte,
                    b'C' => Primitive::Char,
                    b'D' => Primitive::Double,
                    b'F' => Primitive::Float,
                    b'I' => Primitive::Int,
                    b'J' => Primitive::Long,
                    b'S' => Primitive::Short,
                    b'Z' => Primitive::Boolean,
                    _ => return Err(DecompileError::InvalidAttribute("annotation constant")),
                };
                constant_literal_with_options(
                    pool,
                    *index,
                    Some(&Type::Primitive(primitive)),
                    self.options,
                    |name| self.names.render(name),
                )
                .map(Document::from)
                .map_err(|source| DecompileError::Render {
                    context: "annotation constant",
                    source: Box::new(source),
                })
            }
            ElementValue::Enum {
                type_name_index,
                const_name_index,
            } => {
                let descriptor = pool.utf8(*type_name_index)?;
                let ty = parse(descriptor, Type::parse)?;
                let Type::Object(owner) = ty else {
                    return Err(DecompileError::InvalidAttribute("annotation enum type"));
                };
                let mut result = Document::new();
                symbols::append_class(
                    &mut result,
                    &self.names.render(&owner),
                    &owner,
                    self.options.dump_text_tokens,
                );
                let name = pool.utf8(*const_name_index)?;
                result.push('.');
                if self.options.dump_text_tokens {
                    result.token(
                        name,
                        Token {
                            declaration: false,
                            kind: TokenKind::Field {
                                owner,
                                name: name.into(),
                                descriptor: descriptor.into(),
                            },
                        },
                    );
                } else {
                    result.push_str(name);
                }
                Ok(result)
            }
            ElementValue::Class(index) => {
                let descriptor = pool.utf8(*index)?;
                let ty = if descriptor == "V" {
                    Type::Void
                } else {
                    parse(descriptor, Type::parse)?
                };
                let mut result = self.render_type_target(
                    &ty,
                    &[],
                    crate::classfile::TypeTarget::Field,
                    &[],
                    false,
                )?;
                result.push_str(".class");
                Ok(result)
            }
            ElementValue::Annotation(annotation) => self.annotation_document(annotation, None),
            ElementValue::Array(values) => {
                let mut result = Document::from("{");
                for (index, value) in values.iter().enumerate() {
                    if index != 0 {
                        result.push_str(", ");
                    }
                    result.append(self.annotation_value(value)?);
                }
                result.push('}');
                Ok(result)
            }
        }
    }

    fn annotation_member_type(
        &self,
        owner: &str,
        name: &str,
        value: &ElementValue,
    ) -> Result<Option<Cow<'_, str>>, DecompileError> {
        if let Some(class) = self.group.get(owner) {
            for method in &class.methods {
                let pool = &class.pool;
                let descriptor = pool.utf8(method.descriptor_index)?;
                if descriptor.starts_with("()") && pool.utf8(method.name_index)? == name {
                    return Ok(Some(Cow::Borrowed(descriptor)));
                }
            }
        }
        let mut desc = String::from("()");
        let mut value = value;
        while let ElementValue::Array(elements) = value {
            let Some(first) = elements.first() else {
                return Ok(None);
            };
            desc.push('[');
            value = first;
        }
        match value {
            ElementValue::Constant { tag: b's', .. } => desc.push_str("Ljava/lang/String;"),
            ElementValue::Constant { tag, .. } => desc.push(char::from(*tag)),
            ElementValue::Enum {
                type_name_index, ..
            } => desc.push_str(self.class.pool.utf8(*type_name_index)?),
            ElementValue::Class(_) => desc.push_str("Ljava/lang/Class;"),
            ElementValue::Annotation(annotation) => {
                desc.push_str(self.class.pool.utf8(annotation.type_index)?)
            }
            ElementValue::Array(_) => unreachable!("annotation array element type"),
        }
        Ok(Some(Cow::Owned(desc)))
    }
}
