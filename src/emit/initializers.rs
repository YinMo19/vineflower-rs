// Based on Vineflower InitializerProcessor (Apache-2.0).
use std::collections::BTreeMap;

use crate::{
    bytecode::{Operand, decode},
    classfile::find_attribute,
    descriptor::MethodDescriptor,
    lift::{Effect, Machine},
};

use super::{DecompileError, FINAL, STATIC, Writer, parse};

pub(super) struct Initializer {
    pub(super) expression: String,
    pub(super) offsets: Vec<u32>,
}

#[derive(Default)]
pub(super) struct InterfaceInitializers<'a> {
    pub(super) values: BTreeMap<&'a str, Initializer>,
    pub(super) original_lines: Vec<(u16, u16)>,
}

impl<'c> Writer<'_, 'c> {
    pub(super) fn interface_initializers(
        &self,
    ) -> Result<InterfaceInitializers<'c>, DecompileError> {
        let class = self.class;
        let pool = &class.pool;
        let mut fields = Vec::new();
        for field in &class.fields {
            if field.access_flags & (STATIC | FINAL) != STATIC | FINAL {
                return Err(unsupported());
            }
            if find_attribute(&field.attributes, pool, "ConstantValue")?.is_none() {
                fields.push((
                    pool.utf8(field.name_index)?,
                    pool.utf8(field.descriptor_index)?,
                ));
            }
        }
        let mut init = None;
        for method in &class.methods {
            if pool.utf8(method.name_index)? == "<clinit>" && init.replace(method).is_some() {
                return Err(unsupported());
            }
        }
        let Some(init) = init else {
            return if fields.is_empty() {
                Ok(InterfaceInitializers::default())
            } else {
                Err(unsupported())
            };
        };
        let code = init.code(pool)?.ok_or(DecompileError::InvalidAttribute(
            "interface initializer Code",
        ))?;
        if !code.exceptions.is_empty() || pool.utf8(init.descriptor_index)? != "()V" {
            return Err(unsupported());
        }
        let method_error =
            |source: Box<dyn std::error::Error + Send + Sync>| DecompileError::Method {
                name: "<clinit>".into(),
                descriptor: "()V".into(),
                source,
            };
        let map_name = |name: &str| self.names.render(name);
        let descriptor = parse("()V", MethodDescriptor::parse)?;
        let mut machine = Machine::new(class, init, &code, &descriptor, self.options, &map_name)
            .map_err(|source| method_error(Box::new(source)))?;
        let instructions = decode(code.bytes).map_err(|source| method_error(Box::new(source)))?;
        let Some((last, body)) = instructions.split_last() else {
            return Err(unsupported());
        };
        if last.opcode != 0xb1 {
            return Err(unsupported());
        }

        let owner = pool.class_name(class.this_class)?;
        let mut fields = fields.into_iter();
        let mut values = BTreeMap::new();
        let mut offsets = Vec::new();
        for instruction in body {
            let effect = machine
                .step(instruction)
                .map_err(|source| method_error(Box::new(source)))?;
            if !machine.take_prelude().is_empty() {
                return Err(unsupported());
            }
            match effect {
                Effect::None => {
                    if self.mapping.is_some() && instruction.opcode != 0 {
                        offsets.extend(instruction.offset..instruction.offset + instruction.len);
                    }
                }
                Effect::FieldAssignment { target, value }
                    if instruction.opcode == 0xb3 && machine.stack_is_empty() =>
                {
                    let Some((name, descriptor)) = fields.next() else {
                        return Err(unsupported());
                    };
                    let Operand::Constant(index) = instruction.operand else {
                        return Err(unsupported());
                    };
                    if pool.member_ref(index)? != (owner, name, descriptor) || target != name {
                        return Err(unsupported());
                    }
                    values.insert(
                        name,
                        Initializer {
                            expression: value,
                            offsets: std::mem::take(&mut offsets),
                        },
                    );
                }
                _ => return Err(unsupported()),
            }
        }
        if fields.next().is_some() || !machine.stack_is_empty() {
            return Err(unsupported());
        }
        Ok(InterfaceInitializers {
            values,
            original_lines: if self.mapping.is_some() {
                code.line_numbers(pool)?
            } else {
                Vec::new()
            },
        })
    }
}

pub(super) fn unsupported() -> DecompileError {
    DecompileError::Unsupported {
        feature: "interface initialization not expressible as ordered field initializers",
    }
}
