// SPDX-License-Identifier: Apache-2.0

//! ReplaceStatsPass, ReplaceExprentsPass, ResugarKotlinMethodsPass and
//! CollapseStringConcatPass. Traversal follows the owners' expression slots.

use std::io;

use crate::decompiler::exps::{
    Expr, ExprKind, FunctionType, Variable, WriteFlags, allocation_flags,
};
use crate::decompiler::flow::flatten::build_direct_graph;
use crate::decompiler::ir::{ExprId, ExprListId, StatId};
use crate::decompiler::stats::StatementKind;
use crate::engine::{Cx, counter_container::CounterContainer};
use crate::types::VarType;

use super::{Declaration, KotlinExpr, KotlinFunction};

pub(super) fn replace_statements(cx: &mut Cx, counters: &mut CounterContainer, stat: StatId) {
    for index in 0..cx.ir[stat].stats.len() {
        let child = cx.ir[stat].stats[index];
        replace_statements(cx, counters, child);
        if let Some(replacement) = child.replace_with_kotlin(&mut cx.ir, counters) {
            cx.kotlin_body_mut().statements.insert(replacement);
        }
    }
}

pub(super) fn replace_expressions(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    stat: StatId,
) -> io::Result<()> {
    for index in 0..cx.ir[stat].stats.len() {
        replace_expressions(cx, counters, cx.ir[stat].stats[index])?;
    }

    let resources = match &cx.ir[stat].kind {
        StatementKind::Catch {
            vars, resources, ..
        } => Some((vars.clone(), *resources, None)),
        StatementKind::CatchAll { vars, monitor, .. } => Some((vars.clone(), None, *monitor)),
        _ => None,
    };
    let resources = if let Some((vars, resources, monitor)) = resources {
        let vars = vars
            .into_iter()
            .map(|expr| wrap_variable(cx, counters, expr, Some(Declaration::Exception)))
            .collect();
        let monitor = monitor.map(|expr| wrap_variable(cx, counters, expr, None));
        match &mut cx.ir[stat].kind {
            StatementKind::Catch { vars: dst, .. } => *dst = vars,
            StatementKind::CatchAll {
                vars: dst,
                monitor: dst_monitor,
                ..
            } => {
                *dst = vars;
                *dst_monitor = monitor;
            }
            _ => unreachable!(),
        }
        resources
    } else {
        None
    };

    replace_list(cx, counters, cx.ir[stat].exprents)?;
    let mut definitions: Vec<_> = cx.ir[stat]
        .var_definitions
        .iter()
        .copied()
        .map(Some)
        .collect();
    replace_slots(cx, counters, &mut definitions)?;
    cx.ir[stat].var_definitions = definitions.into_iter().flatten().collect();

    match &cx.ir[stat].kind {
        StatementKind::Catch { .. } => replace_list(cx, counters, resources)?,
        StatementKind::Do(data) => {
            let data = *data;
            for list in [data.init, data.condition, data.increment] {
                replace_list(cx, counters, list)?;
            }
        }
        StatementKind::If(data) => replace_list(cx, counters, data.head_exprents)?,
        StatementKind::Switch(data) => {
            let head = data.head_exprents;
            let mut cases: Vec<_> = data.case_values().map(<[_]>::to_vec).collect();
            for case in &mut cases {
                replace_slots(cx, counters, case)?;
            }
            let StatementKind::Switch(data) = &mut cx.ir[stat].kind else {
                unreachable!()
            };
            for (list, replacement) in data.case_values_mut().zip(cases) {
                list.copy_from_slice(&replacement);
            }
            let mut guards = data.case_guards.clone();
            replace_slots(cx, counters, &mut guards)?;
            let StatementKind::Switch(data) = &mut cx.ir[stat].kind else {
                unreachable!()
            };
            data.case_guards = guards;
            replace_list(cx, counters, head)?;
        }
        StatementKind::Synchronized { head_exprents, .. } => {
            replace_list(cx, counters, *head_exprents)?;
        }
        _ => {}
    }
    Ok(())
}

fn replace_list(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    list: Option<ExprListId>,
) -> io::Result<()> {
    let Some(list) = list else { return Ok(()) };
    for index in 0..cx.ir[list].len() {
        let expr = cx.ir[list][index];
        cx.ir[list][index] = wrap(cx, counters, expr)?;
    }
    for index in 0..cx.ir[list].len() {
        replace_children(cx, counters, cx.ir[list][index])?;
    }
    Ok(())
}

fn replace_slots(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    slots: &mut [Option<ExprId>],
) -> io::Result<()> {
    for expr in slots.iter_mut().flatten() {
        *expr = wrap(cx, counters, *expr)?;
    }
    for &expr in slots.iter().flatten() {
        replace_children(cx, counters, expr)?;
    }
    Ok(())
}

fn replace_children(cx: &mut Cx, counters: &mut CounterContainer, expr: ExprId) -> io::Result<()> {
    let children: Vec<_> = Expr::children(&cx.ir, expr).collect();
    for child in children {
        replace_children(cx, counters, child)?;
        let replacement = wrap(cx, counters, child)?;
        if child != replacement {
            Expr::replace(&mut cx.ir, expr, child, replacement);
        }
    }
    Ok(())
}

pub(super) fn wrap_variable(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    original: ExprId,
    declaration: Option<Declaration>,
) -> ExprId {
    let var = Expr::variable(&cx.ir, original).expect("Expected a local variable expression");
    let declaration = declaration.unwrap_or_else(|| match cx.kotlin_expr(original) {
        Some(KotlinExpr::Variable(declaration)) => *declaration,
        _ if var.definition => Declaration::Definition,
        _ => Declaration::Usage,
    });
    // KVarExprent's constructor deliberately does not preserve the LVT.
    let var = Variable {
        processor: var.processor,
        var_type: Some(var.expr_type(cx)),
        version: var.version,
        stack: var.stack,
        class_definition: var.class_definition,
        definition: var.definition,
        effectively_final: var.effectively_final,
        ..Variable::new(var.index, None)
    };
    let offsets = cx.ir[original].bytecode.clone();
    let expr = Expr::new(&mut cx.ir, counters, ExprKind::Variable(var), offsets);
    cx.set_kotlin_expr(expr, KotlinExpr::Variable(declaration));
    expr
}

pub(super) fn wrap(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    original: ExprId,
) -> io::Result<ExprId> {
    if cx.kotlin_expr(original).is_some() {
        return Ok(original);
    }
    wrap_unmarked(cx, counters, original, None, None)
}

fn wrap_unmarked(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    original: ExprId,
    kotlin_function: Option<KotlinFunction>,
    expr_type: Option<VarType>,
) -> io::Result<ExprId> {
    let mut kind = cx.ir[original].kind.clone();
    let wrapper = match &mut kind {
        ExprKind::Variable(_) => return Ok(wrap_variable(cx, counters, original, None)),
        ExprKind::Function {
            op,
            operands,
            implicit_type,
            ..
        } => {
            *implicit_type = Some(Box::new(
                expr_type.unwrap_or_else(|| Expr::expr_type(cx, original)),
            ));
            for operand in operands.iter_mut() {
                *operand = wrap(cx, counters, *operand)?;
            }
            let mut kotlin_function = kotlin_function;
            if *op == FunctionType::Eq
                && [operands[0], operands[1]]
                    .into_iter()
                    .all(|expr| Expr::expr_type(cx, expr) != VarType::VARTYPE_NULL)
            {
                *op = FunctionType::Other;
                kotlin_function = Some(KotlinFunction::IdentityEquals);
            }
            KotlinExpr::Function(kotlin_function)
        }
        ExprKind::Invocation(_) => {
            return Ok(wrap_invocation(cx, counters, original));
        }
        ExprKind::Constant { .. } | ExprKind::Field(_) => super::scalar_wrapper(&mut kind),
        ExprKind::SwitchHead { .. } => KotlinExpr::SwitchHead,
        ExprKind::New {
            new_type,
            lambda,
            method_reference,
            generics,
            ..
        } => {
            (_, *lambda, *method_reference) = allocation_flags(cx, new_type);
            *generics = None;
            KotlinExpr::New {
                in_annotation: false,
            }
        }
        ExprKind::Exit { .. } => KotlinExpr::Exit { lambda_name: None },
        _ => return Ok(original),
    };
    let offsets = cx.ir[original].bytecode.clone();
    let expr = Expr::new(&mut cx.ir, counters, kind, offsets);
    if matches!(wrapper, KotlinExpr::New { .. }) {
        cx.ir[expr].write_flags = cx.ir[original].write_flags & WriteFlags::VARARG;
    }
    cx.set_kotlin_expr(expr, wrapper);
    Ok(expr)
}

fn wrap_invocation(cx: &mut Cx, counters: &mut CounterContainer, original: ExprId) -> ExprId {
    use super::InvocationStyle;
    use crate::kotlin::{
        members::{self, MethodElement},
        metadata::flags::IS_INFIX,
    };

    let copy = Expr::copy_java(cx, counters, original);
    let ExprKind::Invocation(invoke) = &cx.ir[copy].kind else {
        unreachable!()
    };
    let (owner, name, descriptor) = (
        invoke.classname.clone(),
        invoke.name.clone(),
        invoke.string_descriptor().to_owned(),
    );
    let style =
        owner.and_then(
            |owner| match members::invocation(cx, &owner, &name, &descriptor)? {
                (MethodElement::Property(property), method) => Some(InvocationStyle::Property {
                    name: property.name.to_string(),
                    method,
                }),
                (MethodElement::Function(function), _) if IS_INFIX.get(function.flags) => {
                    Some(InvocationStyle::Infix {
                        name: function.name.to_string(),
                        extension: function.receiver_type.is_some(),
                    })
                }
                _ => None,
            },
        );
    cx.set_kotlin_expr(copy, KotlinExpr::Invocation(style));
    copy
}

/// Subclasses that override copy construct another wrapper. KField,
/// KConstant and KSwitchHead inherit a copy that returns a Java object.
pub(crate) fn copy_expression(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    expr: ExprId,
) -> Option<ExprId> {
    match cx.kotlin_expr(expr)?.clone() {
        KotlinExpr::Variable(_) => {
            // KVarExprent invokes super.copy before its own constructor.
            let copy = Expr::copy_java(cx, counters, expr);
            Some(wrap_variable(cx, counters, copy, None))
        }
        KotlinExpr::Function(kotlin_function) => {
            let copy = Expr::copy_java(cx, counters, expr);
            let ty = Expr::expr_type(cx, expr);
            Some(
                wrap_unmarked(cx, counters, copy, kotlin_function, Some(ty))
                    .expect("Kotlin function copies preserve the operand types"),
            )
        }
        KotlinExpr::Invocation(_) => Some(wrap_invocation(cx, counters, expr)),
        KotlinExpr::New { .. } | KotlinExpr::Exit { .. } => {
            let copy = Expr::copy_java(cx, counters, expr);
            Some(
                wrap_unmarked(cx, counters, copy, None, None)
                    .expect("Kotlin allocation and exit copies preserve the expression type"),
            )
        }
        _ => None,
    }
}

pub(super) fn resugar(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    root: StatId,
) -> io::Result<()> {
    let graph = build_direct_graph(&mut cx.ir, root);
    for &node in &graph.order {
        let list = graph[node].exprents;
        for index in 0..cx.ir[list].len() {
            resugar_children(cx, counters, cx.ir[list][index])?;
        }
        let mut index = 0;
        while index < cx.ir[list].len() {
            match resugar_expression(cx, counters, cx.ir[list][index])? {
                Rewrite::Keep => {}
                Rewrite::Replace(expr) => cx.ir[list][index] = expr,
                Rewrite::Discard => {
                    cx.ir[list].remove(index);
                    continue;
                }
            }
            index += 1;
        }
    }
    Ok(())
}

fn resugar_children(cx: &mut Cx, counters: &mut CounterContainer, expr: ExprId) -> io::Result<()> {
    let children: Vec<_> = Expr::children(&cx.ir, expr).collect();
    for child in children {
        resugar_children(cx, counters, child)?;
        if let Rewrite::Replace(replacement) = resugar_expression(cx, counters, child)? {
            Expr::replace(&mut cx.ir, expr, child, replacement);
        }
    }
    Ok(())
}

enum Rewrite {
    Keep,
    Replace(ExprId),
    Discard,
}

fn resugar_expression(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    expr: ExprId,
) -> io::Result<Rewrite> {
    let (op, operands, kotlin_op) = match &cx.ir[expr].kind {
        ExprKind::Invocation(invoke) => match (invoke.classname.as_deref(), invoke.name.as_str()) {
            (
                Some("kotlin/jvm/internal/Intrinsics"),
                "checkNotNullParameter" | "checkNotNullExpressionValue",
            ) if invoke.string_descriptor() == "(Ljava/lang/Object;Ljava/lang/String;)V" => {
                return Ok(Rewrite::Discard);
            }
            (Some("kotlin/jvm/internal/Intrinsics"), "checkNotNull")
                if matches!(
                    invoke.string_descriptor(),
                    "(Ljava/lang/Object;Ljava/lang/String;)V" | "(Ljava/lang/Object;)V"
                ) =>
            {
                return Ok(Rewrite::Discard);
            }
            (Some("kotlin/jvm/internal/Intrinsics"), "areEqual") => {
                let [lhs, rhs, ..] = invoke.parameters[..] else {
                    return Ok(Rewrite::Keep);
                };
                (FunctionType::Eq, vec![lhs, rhs], None)
            }
            (Some("kotlin/jvm/internal/Reflection"), "getOrCreateKotlinClass") => {
                let [class, ..] = invoke.parameters[..] else {
                    return Ok(Rewrite::Keep);
                };
                (
                    FunctionType::Other,
                    vec![class],
                    Some(KotlinFunction::GetKClass),
                )
            }
            _ => return Ok(Rewrite::Keep),
        },
        ExprKind::Function {
            op: FunctionType::Ternary,
            operands,
            ..
        } => {
            let [condition, mut value, fallback] = operands[..] else {
                unreachable!()
            };
            let ExprKind::Function {
                op: FunctionType::Ne,
                operands: cmp,
                ..
            } = &cx.ir[condition].kind
            else {
                return Ok(Rewrite::Keep);
            };
            let [original, null] = cmp[..] else {
                unreachable!()
            };
            if !matches!(&cx.ir[null].kind, ExprKind::Constant { var_type, .. } if *var_type == VarType::VARTYPE_NULL)
            {
                return Ok(Rewrite::Keep);
            }
            if let ExprKind::Invocation(invoke) = &cx.ir[value].kind
                && invoke.is_unboxing_call()
                && let Some(instance) = invoke.instance
            {
                value = instance;
            }
            if Expr::variable(&cx.ir, value).is_none() || !Expr::equals(cx, original, value) {
                return Ok(Rewrite::Keep);
            }
            (
                FunctionType::Other,
                vec![original, fallback],
                Some(KotlinFunction::Elvis),
            )
        }
        _ => return Ok(Rewrite::Keep),
    };
    let mut operands = operands;
    for expr in &mut operands {
        *expr = wrap(cx, counters, *expr)?;
    }
    let replacement = Expr::function(&mut cx.ir, counters, op, operands, None);
    cx.set_kotlin_expr(replacement, KotlinExpr::Function(kotlin_op));
    Ok(Rewrite::Replace(replacement))
}

pub(super) fn collapse_string_concat(cx: &mut Cx, stat: StatId) {
    for index in 0..cx.ir[stat].stats.len() {
        collapse_string_concat(cx, cx.ir[stat].stats[index]);
    }
    let list = match cx.ir[stat].kind {
        StatementKind::BasicBlock { .. } => cx.ir[stat].exprents,
        StatementKind::If(data) => data.head_exprents,
        _ => None,
    };
    if let Some(list) = list {
        for index in 0..cx.ir[list].len() {
            collapse_expression(cx, cx.ir[list][index]);
        }
    }
}

fn collapse_expression(cx: &mut Cx, expr: ExprId) {
    let children: Vec<_> = Expr::children(&cx.ir, expr).collect();
    for &child in &children {
        collapse_expression(cx, child);
    }
    if !is_concatenation(cx, expr) {
        return;
    }
    let mut operands = children.clone();
    for child in children {
        if is_concatenation(cx, child) {
            let index = operands
                .iter()
                .position(|&operand| Expr::equals(cx, child, operand))
                .expect("Original string concatenation operand");
            operands.splice(index..index, Expr::children(&cx.ir, child));
            let index = operands
                .iter()
                .position(|&operand| Expr::equals(cx, child, operand))
                .expect("Original string concatenation operand");
            operands.remove(index);
        }
    }
    let ExprKind::Function {
        op, operands: dst, ..
    } = &mut cx.ir[expr].kind
    else {
        unreachable!()
    };
    *op = FunctionType::Other;
    *dst = operands;
    cx.set_kotlin_expr(
        expr,
        KotlinExpr::Function(Some(KotlinFunction::StringTemplate)),
    );
}

fn is_concatenation(cx: &Cx, expr: ExprId) -> bool {
    match cx.kotlin_expr(expr) {
        Some(KotlinExpr::Function(Some(KotlinFunction::StringTemplate))) => true,
        Some(KotlinExpr::Function(None)) => {
            matches!(
                cx.ir[expr].kind,
                ExprKind::Function {
                    op: FunctionType::StrConcat,
                    ..
                }
            )
        }
        _ => false,
    }
}
