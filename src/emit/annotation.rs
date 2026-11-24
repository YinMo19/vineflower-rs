// Based on Vineflower annotation attributes and AnnotationExprent (Apache-2.0).
use super::{DecompileError, Document, Writer, parse};
use crate::{
    classfile::{Annotation, ElementValue, Member},
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

    pub(super) fn annotation(&self, annotation: &Annotation) -> Result<String, DecompileError> {
        Ok(self.annotation_document(annotation, None)?.into_flat())
    }

    pub(super) fn annotation_document(
        &self,
        annotation: &Annotation,
        depth: Option<usize>,
    ) -> Result<Document, DecompileError> {
        let pool = &self.class.pool;
        let name = self.annotation_type(pool.utf8(annotation.type_index)?)?;
        let mut elements = Vec::with_capacity(annotation.elements.len());
        for (member, value) in &annotation.elements {
            let member = pool.utf8(*member)?;
            let mut doc = Document::new();
            if annotation.elements.len() != 1 || member != "value" {
                doc.push_str(member);
                doc.push_str(" = ");
            }
            match value {
                ElementValue::Annotation(nested) => {
                    doc.append(self.annotation_document(nested, None)?)
                }
                _ => doc.push_str(&self.annotation_value(value)?),
            }
            elements.push(doc);
        }
        Ok(match depth {
            Some(depth) => Document::annotation(depth, &name, elements),
            None => Document::inline_annotation(&name, elements),
        })
    }

    pub(super) fn annotation_value(&self, value: &ElementValue) -> Result<String, DecompileError> {
        let pool = &self.class.pool;
        match value {
            ElementValue::Constant { tag: b's', index } => Ok(string_literal(
                &pool.utf16(*index)?,
                self.options.ascii_strings,
            )),
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
                .map_err(|source| DecompileError::Render {
                    context: "annotation constant",
                    source: Box::new(source),
                })
            }
            ElementValue::Enum {
                type_name_index,
                const_name_index,
            } => {
                let mut result = self.annotation_type(pool.utf8(*type_name_index)?)?;
                result.push('.');
                result.push_str(pool.utf8(*const_name_index)?);
                Ok(result)
            }
            ElementValue::Class(index) => {
                let mut result = self.annotation_type(pool.utf8(*index)?)?;
                result.push_str(".class");
                Ok(result)
            }
            ElementValue::Annotation(annotation) => self.annotation(annotation),
            ElementValue::Array(values) => {
                let mut result = String::from("{");
                for (index, value) in values.iter().enumerate() {
                    if index != 0 {
                        result.push_str(", ");
                    }
                    result.push_str(&self.annotation_value(value)?);
                }
                result.push('}');
                Ok(result)
            }
        }
    }

    fn annotation_type(&self, desc: &str) -> Result<String, DecompileError> {
        if desc == "V" {
            return Ok("void".into());
        }
        Ok(parse(desc, Type::parse)?.render(|name| self.names.render(name)))
    }
}
