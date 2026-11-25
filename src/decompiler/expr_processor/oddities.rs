// Copyright 2000-2024 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Diagnostics for residual expressions that would make the method invalid Java.

use std::io;
use std::sync::Arc;

use arcstr::ArcStr;

use super::get_cast_type_name;
use crate::decompiler::assertions::assertion_field;
use crate::decompiler::exps::{ConstantValue, Expr, ExprKind, FunctionType};
use crate::decompiler::ir::{ExprId, StatId};
use crate::decompiler::stats::StatementKind;
use crate::engine::Cx;
use crate::structs::StructClass;
use crate::types::{CodeType, VarType};

const VARIABLE_TYPE_WARNING: &str = "$VF: Could not properly define all variable types!";

pub(crate) fn mark_expr_oddities(cx: &mut Cx, root: StatId, class: &StructClass) -> io::Result<()> {
    cx.with_locked_imports(|cx| mark_statement(cx, root, root, class))
}

fn mark_statement(cx: &mut Cx, root: StatId, stat: StatId, class: &StructClass) -> io::Result<()> {
    for index in 0..cx.ir[stat].stats.len() {
        mark_statement(cx, root, cx.ir[stat].stats[index], class)?;
    }
    for index in 0..cx.ir[stat].var_definitions.len() {
        mark_expression(cx, root, cx.ir[stat].var_definitions[index], class, true)?;
    }
    if matches!(cx.ir[stat].kind, StatementKind::BasicBlock { .. }) {
        if stat.is_labeled(&cx.ir) {
            cx.ir[root].add_comment("$VF: Made invalid labels!", true);
        }
        let exprs = cx.ir[stat]
            .exprents
            .expect("Basic block has no expressions");
        for index in 0..cx.ir[exprs].len() {
            mark_expression(cx, root, cx.ir[exprs][index], class, true)?;
        }
    }
    if let StatementKind::If(branch) = &cx.ir[stat].kind {
        let head = branch
            .head_exprents
            .and_then(|list| cx.ir[list].first().copied())
            .expect("If statement has no condition");
        mark_expression(cx, root, head, class, false)?;
    }
    Ok(())
}

fn mark_expression(
    cx: &mut Cx,
    root: StatId,
    expr: ExprId,
    class: &StructClass,
    block: bool,
) -> io::Result<()> {
    match cx.ir[expr].kind {
        ExprKind::Monitor { .. } => cx.ir[root].add_comment(
            "$VF: Could not create synchronized statement, marking monitor enters and exits",
            true,
        ),
        ExprKind::If { .. } if block => cx.ir[root].add_comment(
            "$VF: Accidentally destroyed if statement, the decompiled code is not correct!",
            true,
        ),
        _ => {}
    }

    let assertion = assertion_field(cx, class).and_then(|(holder, field)| {
        let initializer = holder.method_properties("<clinit> ()V")?;
        (!Arc::ptr_eq(root.method(&cx.ir), &initializer.mt))
            .then(|| (holder.qualified_name.clone(), field.name.clone()))
    });
    for expr in Expr::all_exprents(&cx.ir, expr, true, true) {
        match &cx.ir[expr].kind {
            ExprKind::Variable(var) => {
                let definition_type = var.definition.then(|| var.definition_var_type(cx));
                if definition_type
                    .is_some_and(|ty| is_invalid_type_name(&definition_type_name(cx, &ty)))
                    || is_unknown_type(&Expr::expr_type(cx, expr))
                {
                    cx.ir[root].add_comment(VARIABLE_TYPE_WARNING, true);
                }
            }
            ExprKind::Function {
                op: FunctionType::Cast,
                operands,
                needs_cast: true,
                ..
            } => {
                let target = operands[1];
                if is_invalid_type_name(&cast_operand_string(cx, target)?) {
                    cx.ir[root].add_comment(VARIABLE_TYPE_WARNING, true);
                }
            }
            ExprKind::Field(field)
                if assertion.as_ref().is_some_and(|(owner, name)| {
                    field.classname.as_ref() == Some(owner) && &field.name == name
                }) =>
            {
                cx.ir[root].add_comment("$VF: Could not resugar all assert statements!", true);
            }
            _ => {}
        }
    }
    Ok(())
}

fn definition_type_name(cx: &mut Cx, ty: &VarType) -> String {
    let name = get_cast_type_name(cx, ty);
    if name == "<unrepresentable>" {
        "var".to_owned()
    } else {
        name
    }
}

fn is_invalid_type_name(name: &str) -> bool {
    matches!(name, "<undefinedtype>" | "<null>" | "<unknown>")
}

fn is_unknown_type(ty: &VarType) -> bool {
    let unknown = VarType::VARTYPE_UNKNOWN;
    // The stored descriptor of the singleton survives type cloning. A type
    // freshly parsed from a debug descriptor must not replace that identity.
    ty == &unknown && ArcStr::ptr_eq(ty.value.as_ref().unwrap(), unknown.value.as_ref().unwrap())
}

fn cast_operand_string(cx: &mut Cx, expr: ExprId) -> io::Result<String> {
    // CHECKCAST and the passes that combine its targets use valueless
    // ConstExprents. ConstExprent.toString renders the type before wrapping it,
    // which can resolve classes even with import writes locked.
    let ExprKind::Constant {
        value: ConstantValue::Null,
        var_type,
        was_condy,
        ..
    } = &cx.ir[expr].kind
    else {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "Cast target is not a type constant",
        ));
    };
    let ty = var_type.clone();
    let prefix = if *was_condy {
        "/* $VF: constant dynamic */ "
    } else {
        ""
    };
    let name = if ty.ty == CodeType::Null {
        "null".to_owned()
    } else {
        get_cast_type_name(cx, &ty)
    };
    Ok(format!("const({prefix}{name})"))
}
