// Based on Vineflower annotation attributes and AnnotationExprent (Apache-2.0).
use super::{DecompileError, Writer, parse};
use crate::{
    classfile::{Annotation, ElementValue, Member},
    descriptor::{Primitive, Type},
    lift::{constant_literal, string_literal},
};

impl<'a> Writer<'a, '_> {
    pub(super) fn class_annotations(&mut self, depth: usize) -> Result<(), DecompileError> {
        for visible in [true, false] {
            for annotation in self.class.annotations(visible)? {
                self.line(depth, &self.annotation(&annotation)?);
            }
        }
        Ok(())
    }

    pub(super) fn annotations_of(
        &self,
        member: &Member<'a>,
    ) -> Result<Vec<String>, DecompileError> {
        let mut result = Vec::new();
        for visible in [true, false] {
            for annotation in member.annotations(&self.class.pool, visible)? {
                result.push(self.annotation(&annotation)?);
            }
        }
        Ok(result)
    }

    pub(super) fn member_annotations(
        &mut self,
        depth: usize,
        member: &Member<'a>,
    ) -> Result<(), DecompileError> {
        for annotation in self.annotations_of(member)? {
            self.line(depth, &annotation);
        }
        Ok(())
    }

    pub(super) fn annotation(&self, annotation: &Annotation) -> Result<String, DecompileError> {
        let pool = &self.class.pool;
        let mut result = String::from("@");
        result.push_str(&self.annotation_type(pool.utf8(annotation.type_index)?)?);
        if !annotation.elements.is_empty() {
            result.push('(');
            for (index, (name, value)) in annotation.elements.iter().enumerate() {
                if index != 0 {
                    result.push_str(", ");
                }
                let name = pool.utf8(*name)?;
                if annotation.elements.len() != 1 || name != "value" {
                    result.push_str(name);
                    result.push_str(" = ");
                }
                result.push_str(&self.annotation_value(value)?);
            }
            result.push(')');
        }
        Ok(result)
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
                constant_literal(
                    pool,
                    *index,
                    Some(&Type::Primitive(primitive)),
                    self.options.ascii_strings,
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
