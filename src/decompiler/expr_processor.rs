// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Bytecode expressions used by finally analysis and method decompilation.

mod block;
mod casts;
pub(crate) use casts::canonicalize_casts;
mod condy;
mod driver;
mod oddities;

pub(crate) use driver::process_statement;
pub(crate) use oddities::mark_expr_oddities;

use crate::decompiler::ir::{ExprId, VarProcessorId};
use crate::engine::{Cx, import_collector};
use crate::types::{CodeType, VarType};

struct ExpressionData {
    variables: VarProcessorId,
    stack: Vec<ExprId>,
    expressions: Vec<ExprId>,
}

/// ExprProcessor.getCastTypeName, including the array rank of the outer type.
pub fn get_cast_type_name(cx: &mut Cx, ty: &VarType) -> String {
    cast_type_name(cx, ty, true)
}

pub(crate) fn cast_type_name(cx: &mut Cx, ty: &VarType, short: bool) -> String {
    let mut name = type_name(cx, ty, short);
    for _ in 0..ty.array_dim {
        name.push_str("[]");
    }
    name
}

/// ExprProcessor.getTypeName spells the element type. Array brackets belong to the caller.
pub(crate) fn type_name(cx: &mut Cx, ty: &VarType, short: bool) -> String {
    match ty.ty {
        CodeType::Object if ty.is_generic() => ty.get_cast_name(cx),
        CodeType::Object => {
            let name = ty.name();
            let dotted = import_collector::java_class_name(cx, name);
            if short {
                import_collector::get_short_name(cx, &dotted)
            } else {
                dotted
            }
        }
        CodeType::Genvar if ty.is_generic() => ty.name().to_owned(),
        other => match other {
            CodeType::Byte => "byte",
            CodeType::Char => "char",
            CodeType::Double => "double",
            CodeType::Float => "float",
            CodeType::Int => "int",
            CodeType::Long => "long",
            CodeType::Short => "short",
            CodeType::Boolean => "boolean",
            CodeType::Void => "void",
            CodeType::Unknown => "<unknown>",
            CodeType::Null => "<null>",
            CodeType::Bytechar => "<bytechar>",
            CodeType::Shortchar => "<shortchar>",
            other => panic!("invalid type: {other:?}"),
        }
        .to_owned(),
    }
}
