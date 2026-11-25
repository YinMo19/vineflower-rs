// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Bytecode expressions used by finally analysis and method decompilation.

mod block;
mod condy;
mod driver;

pub(crate) use driver::process_statement;

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
    let mut name = match ty.ty {
        CodeType::Object if ty.is_generic() => ty.get_cast_name(cx),
        CodeType::Object => {
            let name = ty.name();
            let mut dotted = name.replace('/', ".");
            if name.contains('$')
                && !cx
                    .classes()
                    .get_class(name)
                    .is_some_and(|class| class.own)
            {
                dotted = dotted.replace('$', ".");
            }
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
    };
    for _ in 0..ty.array_dim {
        name.push_str("[]");
    }
    name
}
