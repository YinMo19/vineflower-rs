// Copyright 2000-2024 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! `GenericsProcessor.qualifyChains`.

use std::io;

use super::exps::{Expr, ExprKind, Invocation, generic_inference::Inference};
use super::ir::{ExprId, StatId};
use crate::engine::Cx;

pub(crate) fn qualify_chains(cx: &mut Cx, root: StatId) -> io::Result<bool> {
    // ClassWrapper.init sets the active class and VarProcessor. Its method
    // wrappers are not yet published, and CURRENT_METHOD_WRAPPER is unset.
    let method = root.method(&cx.ir).clone();
    qualify_statement(&mut Inference::at_end(cx, method), root)
}

fn qualify_statement(inference: &mut Inference<'_>, stat: StatId) -> io::Result<bool> {
    let mut changed = false;
    if let Some(list) = inference.cx.ir[stat].exprents {
        for expr in inference.cx.ir[list].clone() {
            changed |= qualify_expr(inference, expr)?;
        }
    }
    let children: Vec<_> = inference.cx.ir[stat].stats.iter().copied().collect();
    for child in children {
        changed |= qualify_statement(inference, child)?;
    }
    Ok(changed)
}

fn qualify_expr(inference: &mut Inference<'_>, expr: ExprId) -> io::Result<bool> {
    let mut changed = false;
    let children: Vec<_> = Expr::children(&inference.cx.ir, expr).collect();
    for child in children {
        changed |= qualify_expr(inference, child)?;
    }
    if matches!(inference.cx.ir[expr].kind, ExprKind::Invocation(_)) {
        changed |= qualify_invocation(inference, expr)?;
    }
    Ok(changed)
}

fn qualify_invocation(inference: &mut Inference<'_>, expr: ExprId) -> io::Result<bool> {
    let mut chain = Vec::new();
    let mut next = Some(expr);
    while let Some(id) = next {
        let ExprKind::Invocation(call) = &inference.cx.ir[id].kind else {
            break;
        };
        chain.push(id);
        next = call.instance;
    }
    if chain.len() < 2 {
        return Ok(false);
    }

    let base = *chain.last().unwrap();
    let ExprKind::Invocation(call) = &inference.cx.ir[base].kind else {
        unreachable!()
    };
    let found_lambda = call.parameters.iter().any(|&id| {
        matches!(
            inference.cx.ir[id].kind,
            ExprKind::New {
                lambda: true,
                method_reference: false,
                ..
            }
        ) || inference.has_overloaded_method_reference(id)
    });
    if !found_lambda {
        return Ok(false);
    }
    let erased_return = call.descriptor.ret.clone();

    inference.infer(base, None)?;
    let Some(base_signature) =
        Invocation::resolve_description(inference.cx, base).and_then(|method| method.signature())
    else {
        return Ok(false);
    };
    for &id in &chain {
        let ExprKind::Invocation(call) = &inference.cx.ir[id].kind else {
            unreachable!()
        };
        if !call
            .descriptor
            .ret
            .higher_equal_in_lattice_than(inference.cx, &erased_return)
        {
            return Ok(false);
        }
    }
    for id in chain {
        inference.infer(id, None)?;
        let Some(signature) =
            Invocation::resolve_description(inference.cx, id).and_then(|method| method.signature())
        else {
            return Ok(false);
        };
        if signature
            .type_parameters
            .iter()
            .any(|name| base_signature.type_parameters.contains(name))
        {
            // Java updates this flag after inference. The next inference of
            // the base renders its arguments with explicit qualification.
            inference.invocation_state(base).force_qualification = true;
            return Ok(true);
        }
    }
    Ok(false)
}
