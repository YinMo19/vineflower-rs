//! NewExprent.setLambdaGenericTypes publishes the SAM's inferred signature
//! into the method body immediately before ClassWriter renders the lambda.

use super::invalid;
use crate::decompiler::{
    exps::{ExitType, ExprKind},
    ir::{ExprId, StatId, VarProcessorId},
    stats::StatementKind,
    vars::var_version_pair::VarVersionPair,
};
use crate::engine::{
    Cx,
    class_nodes::{ClassKind, ClassNodeId},
    class_wrapper::MethodSlot,
};
use crate::types::{
    GenericMethodDescriptor, GenericsMap, MethodDescriptor, SharedSignature, VarType,
};
use std::{collections::VecDeque, io};

pub(super) fn set(
    cx: &mut Cx,
    expr: ExprId,
    node: ClassNodeId,
    constructor: Option<ExprId>,
) -> io::Result<()> {
    let ExprKind::New {
        generics: Some(state),
        ..
    } = &cx.ir[expr].kind
    else {
        return Ok(());
    };
    let Some(mut inferred) = state.inferred_lambda_type.clone() else {
        return Ok(());
    };
    let Some(mut interface) = cx.classes().get_class(inferred.name()) else {
        return Ok(());
    };
    let info = cx.class_nodes[node]
        .lambda
        .clone()
        .ok_or_else(|| invalid("Missing lambda method metadata"))?;
    let Some(constructor) = constructor else {
        return Ok(());
    };
    let ExprKind::Invocation(call) = &cx.ir[constructor].kind else {
        return Err(invalid("Missing lambda factory invocation"));
    };
    let Some(sam) = interface
        .get_method(&info.method_name, call.lambda_sam_descriptor()?)
        .cloned()
    else {
        return Ok(());
    };
    let Some(signature) = sam.signature() else {
        return Ok(());
    };
    let Some(method) = MethodSlot::by_key(cx, node, &info.content_method_key) else {
        return Ok(());
    };
    let wrapper = method.get(cx);
    let Some(root) = wrapper.root() else {
        return Ok(());
    };
    let variables = wrapper.variables;
    if sam.class_qualified_name != inferred.name() {
        let candidate = cx
            .classes()
            .get_class(&sam.class_qualified_name)
            .ok_or_else(|| invalid("Missing lambda interface declaring class"))?;
        if let Some(sig) = candidate.signature() {
            inferred = VarType::get_generic_super_type(cx, &inferred, &sig.generic_type);
            if let ExprKind::New {
                generics: Some(state),
                ..
            } = &mut cx.ir[expr].kind
            {
                state.inferred_lambda_type = Some(inferred.clone());
            }
            interface = candidate;
        }
    }
    let mut map = GenericsMap::new();
    if inferred.is_generic() {
        let sig = interface
            .signature()
            .ok_or_else(|| invalid("Missing generic lambda interface signature"))?;
        sig.generic_type.map_gen_vars_to(cx, &inferred, &mut map);
    }

    let content = MethodDescriptor::parse_descriptor(&info.content_method_descriptor);
    let functional = MethodDescriptor::parse_descriptor(&info.method_descriptor);
    let captured = content.params.len().saturating_sub(functional.params.len());
    for (i, (slot, _)) in content
        .parameter_slots(info.is_content_method_static)
        .skip(captured)
        .enumerate()
    {
        let pair = VarVersionPair::new(slot, 0);
        let param = signature
            .parameter_types
            .get(i)
            .ok_or_else(|| invalid("Missing lambda SAM parameter"))?;
        if let Some(old) = cx.ir[variables].versions.lower.get(&pair)
            && let Some(ty) = remapped_type(param, &map, old)
        {
            cx.ir[variables].versions.lower.insert(pair, ty.clone());
            propagate_parameter(cx, node, variables, pair, &ty)?;
        }
    }
    if let Some(ty) = remapped_type(&signature.return_type, &map, &content.ret) {
        replace_return_type(cx, root, ty);
    }
    Ok(())
}

fn remapped_type(formal: &VarType, map: &GenericsMap, old: &VarType) -> Option<VarType> {
    formal.remap_for_inference(map).filter(|ty| {
        *ty != VarType::VARTYPE_VOID && (ty != old || ty.is_generic() && !ty.equals_exact(old))
    })
}

fn propagate_parameter(
    cx: &mut Cx,
    node: ClassNodeId,
    variables: VarProcessorId,
    pair: VarVersionPair,
    ty: &VarType,
) -> io::Result<()> {
    let name = cx.ir[variables].names.get(&pair).cloned().flatten();
    let mut children: VecDeque<_> = cx.class_nodes[node].nested.iter().copied().collect();
    while let Some(child) = children.pop_front() {
        let child = &cx.class_nodes[child];
        children.extend(child.nested.iter().copied());
        if child.kind == ClassKind::Lambda
            && let Some(info) = child
                .lambda
                .as_ref()
                .filter(|info| !info.is_method_reference)
            && let Some(slot) = MethodSlot::by_key(cx, node, &info.content_method_key)
        {
            let other = slot.get(cx).variables;
            let name = name
                .as_ref()
                .ok_or_else(|| invalid("Missing name for lambda parameter"))?;
            if cx.ir[other].names.get(&pair).and_then(Option::as_ref) == Some(name) {
                cx.ir[other].versions.lower.insert(pair, ty.clone());
            }
        }
    }
    Ok(())
}

fn replace_return_type(cx: &Cx, root: StatId, ty: VarType) {
    let StatementKind::Root { dummy_exit, .. } = cx.ir[root].kind else {
        unreachable!()
    };
    // All returns from this invocation of codeToJava own the same method descriptor.
    for &edge in cx.ir[dummy_exit].all_predecessors() {
        let source = cx.ir[edge].source;
        if let Some(&last) = cx.ir[source].exprents.and_then(|list| cx.ir[list].last())
            && let ExprKind::Exit {
                kind: ExitType::Return,
                method_descriptor,
                ..
            } = &cx.ir[last].kind
        {
            method_descriptor.add_generic_descriptor(SharedSignature::new(
                GenericMethodDescriptor {
                    type_parameters: vec![],
                    type_parameter_bounds: vec![],
                    parameter_types: vec![],
                    return_type: ty,
                    exception_types: vec![],
                },
            ));
            break;
        }
    }
}
