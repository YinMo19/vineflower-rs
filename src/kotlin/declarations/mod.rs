// SPDX-License-Identifier: Apache-2.0

//! Kotlin declaration types read from the metadata attached to JVM classes.

mod contract;
pub use contract::KContract;

use std::{fmt, io};

use arcstr::ArcStr;

use super::metadata::{NameResolver, flags, proto};
use super::{identifier, types::java_signature};
use crate::engine::{Cx, import_collector::get_short_name};
use crate::types::VarType;
use crate::util::text_buffer::TextBuffer;

use proto::{r#type::argument::Projection, type_parameter::Variance};

#[derive(Clone, Debug)]
pub struct KType {
    pub jvm: VarType,
    pub classifier: ArcStr,
    pub nullable: bool,
    pub unsigned: bool,
    pub arguments: Vec<TypeArgument>,
    pub parameter_name: Option<ArcStr>,
    pub alias_name: Option<ArcStr>,
}

#[derive(Clone, Debug)]
pub struct TypeArgument {
    pub ty: KType,
    pub projection: Projection,
}

pub(super) fn resolve(names: &NameResolver, id: i32) -> io::Result<ArcStr> {
    names
        .resolve(id)
        .map(|name| name.as_utf8_lossy().clone())
        .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))
}

impl KType {
    pub fn from_proto(proto: Option<&proto::Type>, names: &NameResolver) -> io::Result<Self> {
        let default;
        let proto = match proto {
            Some(ty) => ty,
            None => {
                default = proto::Type::default();
                &default
            }
        };
        let classifier = proto
            .class_name
            .map(|id| resolve(names, id))
            .transpose()?
            .unwrap_or_else(|| arcstr::literal!("kotlin/Any"));
        let nullable = proto.nullable();
        if !nullable && let Some(ty) = Self::builtin(&classifier) {
            return Ok(ty);
        }
        let arguments = proto
            .argument
            .iter()
            .map(|arg| {
                Ok(TypeArgument {
                    ty: Self::from_proto(arg.r#type.as_ref(), names)?,
                    projection: arg.projection(),
                })
            })
            .collect::<io::Result<Vec<_>>>()?;
        let descriptor = if classifier == "kotlin/Array" {
            let first = arguments
                .first()
                .ok_or_else(|| io::Error::other("Kotlin Array is missing its element type"))?;
            if first.projection == Projection::In {
                "[Ljava/lang/Object;".to_owned()
            } else {
                format!("[{}", first.ty)
            }
        } else {
            java_signature(&classifier, nullable)
        };
        Ok(Self {
            jvm: VarType::from_signature(&descriptor),
            classifier,
            nullable,
            unsigned: false,
            arguments,
            parameter_name: proto
                .type_parameter_name
                .map(|id| resolve(names, id))
                .transpose()?,
            alias_name: proto
                .type_alias_name
                .map(|id| resolve(names, id))
                .transpose()?,
        })
    }

    pub fn from_table(
        index: i32,
        table: &proto::TypeTable,
        names: &NameResolver,
    ) -> io::Result<Self> {
        let ty = table.r#type.get(index as usize).ok_or_else(|| {
            io::Error::other(format!("Missing Kotlin metadata type at index {index}"))
        })?;
        Self::from_proto(Some(ty), names)
    }

    /// The plugin recognizes these non-null types before examining their arguments.
    pub fn builtin(classifier: &str) -> Option<Self> {
        let (jvm, unsigned) = match classifier {
            "kotlin/Unit" => (VarType::VARTYPE_VOID, false),
            "kotlin/Nothing" => (VarType::from_signature("Ljava/lang/Void;"), false),
            "kotlin/UByte" => (VarType::VARTYPE_BYTE, true),
            "kotlin/UShort" => (VarType::VARTYPE_SHORT, true),
            "kotlin/UInt" => (VarType::VARTYPE_INT, true),
            "kotlin/ULong" => (VarType::VARTYPE_LONG, true),
            _ => return None,
        };
        Some(Self {
            jvm,
            classifier: classifier.into(),
            nullable: false,
            unsigned,
            arguments: Vec::new(),
            parameter_name: None,
            alias_name: None,
        })
    }

    pub fn write(&self, cx: &mut Cx, buf: &mut TextBuffer, indent: i32) -> io::Result<()> {
        if let Some(name) = &self.parameter_name {
            buf.append(name);
        } else if self.classifier.starts_with("kotlin/Function") {
            let (ret, params) = self.arguments.split_last().ok_or_else(|| {
                io::Error::other("Kotlin function type is missing its return type")
            })?;
            buf.append(if self.nullable { "((" } else { "(" });
            write_arguments(cx, buf, params, indent, "")?;
            buf.append(") -> ");
            ret.write(cx, buf, indent + 1)?;
            if self.nullable {
                buf.append_char(')');
            }
        } else {
            buf.append(&get_short_name(cx, &self.classifier.replace('/', ".")));
            if !self.arguments.is_empty() {
                buf.append_char('<');
                write_arguments(cx, buf, &self.arguments, indent, ">")?;
            }
        }
        if self.nullable {
            buf.append_char('?');
        }
        Ok(())
    }
}

impl fmt::Display for KType {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.jvm.fmt(formatter)
    }
}

fn write_arguments(
    cx: &mut Cx,
    buffer: &mut TextBuffer,
    args: &[TypeArgument],
    indent: i32,
    closing: &str,
) -> io::Result<()> {
    buffer
        .push_newline_group(indent, 1)
        .append_possible_newline();
    for (index, arg) in args.iter().enumerate() {
        if index > 0 {
            buffer
                .append_char(',')
                .append_possible_newline_or(" ", false);
        }
        arg.write(cx, buffer, indent + 1)?;
    }
    buffer
        .append_possible_newline_or("", true)
        .append(closing)
        .pop_newline_group();
    Ok(())
}

impl TypeArgument {
    fn write(&self, cx: &mut Cx, buffer: &mut TextBuffer, indent: i32) -> io::Result<()> {
        match self.projection {
            Projection::Star => {
                buffer.append_char('*');
                return Ok(());
            }
            Projection::In => {
                buffer.append("in ");
            }
            Projection::Out => {
                buffer.append("out ");
            }
            Projection::Inv => {}
        }
        self.ty.write(cx, buffer, indent)
    }
}

#[derive(Clone, Debug)]
pub struct KTypeParameter {
    pub reified: bool,
    pub variance: Variance,
    pub upper_bounds: Vec<KType>,
    pub name: ArcStr,
    pub id: i32,
}

impl KTypeParameter {
    pub fn from_proto(proto: &proto::TypeParameter, names: &NameResolver) -> io::Result<Self> {
        Ok(Self {
            reified: proto.reified(),
            variance: proto.variance(),
            upper_bounds: proto
                .upper_bound
                .iter()
                .map(|ty| KType::from_proto(Some(ty), names))
                .collect::<io::Result<_>>()?,
            name: resolve(names, proto.name())?,
            id: proto.id(),
        })
    }
}

#[derive(Clone, Debug)]
pub struct KParameter {
    pub flags: i32,
    pub name: ArcStr,
    pub ty: KType,
    pub vararg_type: Option<KType>,
    pub type_id: i32,
}

impl KParameter {
    pub fn for_function(proto: &proto::ValueParameter, names: &NameResolver) -> io::Result<Self> {
        Self::read(proto, names, false)
    }

    pub fn for_constructor(
        proto: &proto::ValueParameter,
        names: &NameResolver,
    ) -> io::Result<Self> {
        // KConstructor calls getVarargElementType even on an absent field.
        Self::read(proto, names, true)
    }

    fn read(
        proto: &proto::ValueParameter,
        names: &NameResolver,
        default_vararg: bool,
    ) -> io::Result<Self> {
        let name = resolve(names, proto.name())?;
        let ty = KType::from_proto(proto.r#type.as_ref(), names)?;
        let vararg_type = (default_vararg || proto.vararg_element_type.is_some())
            .then(|| KType::from_proto(proto.vararg_element_type.as_ref(), names))
            .transpose()?;
        Ok(Self {
            flags: proto.flags(),
            name,
            ty,
            vararg_type,
            type_id: proto.type_id(),
        })
    }

    pub fn write(&self, cx: &mut Cx, buffer: &mut TextBuffer, indent: i32) -> io::Result<()> {
        if flags::IS_CROSSINLINE.get(self.flags) {
            buffer.append("crossinline ");
        }
        if flags::IS_NOINLINE.get(self.flags) {
            buffer.append("noinline ");
        }
        let declared = if let Some(element) = self
            .vararg_type
            .as_ref()
            .filter(|_| self.ty.classifier == "kotlin/Array")
        {
            buffer.append("vararg ");
            element
        } else {
            &self.ty
        };
        buffer.append(&identifier(&self.name)).append(": ");
        declared.write(cx, buffer, indent + 1)
    }
}
