// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Discover `LambdaMetafactory` call sites and attach their class nodes.

use std::{io, sync::Arc};

use arcstr::ArcStr;
use rustc_hash::FxHashMap;

use super::{ClassKind, ClassNode, ClassNodeId, ClassNodes, LambdaInformation};
use crate::code::code_constants::{
    CONSTANT_INVOKEDYNAMIC, CONSTANT_METHODHANDLE, CONSTANT_METHODHANDLE_REF_INVOKESTATIC,
    CONSTANT_METHODTYPE, OPC_INVOKEDYNAMIC,
};
use crate::structs::consts::{ConstantValue, LinkConstant, PooledConstant, PrimitiveConstant};
use crate::structs::struct_member::StructMember;
use crate::structs::{StructClass, StructMethod};
use crate::types::{MethodDescriptor, VarType};
use crate::util::interpreter_util::make_unique_key;

/// `LambdaProcessor.processClass`, before the class wrappers process methods.
pub fn process_lambdas(nodes: &mut ClassNodes, root: ClassNodeId) -> io::Result<()> {
    // Scan existing descendants before creating any lambda children here.
    for child in nodes[root].nested.clone() {
        process_lambdas(nodes, child)?;
    }

    let class = Arc::clone(&nodes[root].class);
    if !class.version.has_lambdas() {
        return Ok(());
    }
    let Some(bootstrap) = &class.attributes.bootstrap_methods else {
        return Ok(());
    };
    let lambda_methods: Vec<_> = bootstrap
        .method_refs
        .iter()
        .map(is_lambda_bootstrap)
        .collect();
    if !lambda_methods.iter().any(|&is_lambda| is_lambda) {
        return Ok(());
    }

    let mut lambda_by_content_method = FxHashMap::default();
    for method in &class.methods {
        let Some(seq) = method.expand_data(&class)? else {
            continue;
        };
        for instr in seq.iter().filter(|instr| instr.opcode == OPC_INVOKEDYNAMIC) {
            let Some(PooledConstant::Link(
                dynamic @ LinkConstant {
                    ty: CONSTANT_INVOKEDYNAMIC,
                    ..
                },
            )) = class.pool.get_constant(instr.operand(0))
            else {
                return Err(invalid_data(format!(
                    "Missing invokedynamic constant in {method}"
                )));
            };
            let bootstrap_index = dynamic.index1 as usize;
            if !lambda_methods
                .get(bootstrap_index)
                .copied()
                .unwrap_or(false)
            {
                continue;
            }

            let args = bootstrap
                .method_arguments
                .get(bootstrap_index)
                .ok_or_else(|| {
                    invalid_data(format!("Missing lambda bootstrap arguments in {method}"))
                })?;
            let name: ArcStr = format!(
                "{}##Lambda_{}_{}",
                class.qualified_name, dynamic.index1, dynamic.index2,
            )
            .into();
            let lambda = lambda_node(&class, method, root, name.clone(), dynamic, args)?;
            // Each call site contributes its own node. A repeated synthetic
            // name resolves to the last call site while earlier nodes survive.
            let child = nodes.insert(name.clone(), lambda);
            nodes[root].nested.push(child);
            let info = nodes[child].lambda.as_ref().unwrap();
            if !info.is_method_reference {
                lambda_by_content_method.insert(info.content_method_key.clone(), name);
            }
        }
    }

    nodes.sort_nested(root);
    for child in nodes[root].nested.clone() {
        let lambda = &nodes[child];
        if lambda.kind != ClassKind::Lambda {
            continue;
        }
        let Some(parent_name) = lambda
            .enclosing_method
            .as_ref()
            .and_then(|method| lambda_by_content_method.get(method))
        else {
            continue;
        };
        let parent = nodes
            .id(parent_name)
            .ok_or_else(|| invalid_data(format!("Missing enclosing lambda {parent_name}")))?;
        if parent == child {
            return Err(invalid_data(format!(
                "Lambda {} is recursive?!",
                lambda.class.qualified_name
            )));
        }
        // Keep the original owner's list and establish the additional link.
        nodes[parent].nested.push(child);
        nodes[child].parent = Some(parent);
    }
    Ok(())
}

fn is_lambda_bootstrap(method: &LinkConstant) -> bool {
    method.classname.as_deref() == Some("java/lang/invoke/LambdaMetafactory")
        && matches!(
            method.elementname.as_str(),
            "metafactory" | "altMetafactory"
        )
}

fn lambda_node(
    class: &Arc<StructClass>,
    enclosing: &StructMethod,
    parent: ClassNodeId,
    name: ArcStr,
    dynamic: &LinkConstant,
    args: &[Option<PooledConstant>],
) -> io::Result<ClassNode> {
    let Some(Some(PooledConstant::Primitive(PrimitiveConstant {
        ty: CONSTANT_METHODTYPE,
        value: ConstantValue::String(method_descriptor),
        ..
    }))) = args.get(2)
    else {
        return Err(invalid_data(format!(
            "Missing lambda method type for {name}"
        )));
    };
    let Some(Some(PooledConstant::Link(
        handle @ LinkConstant {
            ty: CONSTANT_METHODHANDLE,
            ..
        },
    ))) = args.get(1)
    else {
        return Err(invalid_data(format!(
            "Missing lambda content method handle for {name}"
        )));
    };
    let content_class_name = handle
        .classname
        .clone()
        .ok_or_else(|| invalid_data(format!("Missing lambda content class for {name}")))?;
    let is_method_reference = if class.qualified_name == content_class_name {
        let target = class
            .get_method(&handle.elementname, &handle.descriptor)
            .ok_or_else(|| {
                invalid_data(format!(
                    "Missing lambda content method {} {} in {}",
                    handle.elementname, handle.descriptor, class.qualified_name
                ))
            })?;
        !target.is_synthetic()
    } else {
        true
    };
    let factory = MethodDescriptor::parse_descriptor(&dynamic.descriptor);
    let lambda_class = factory
        .ret
        .value
        .as_deref()
        .ok_or_else(|| invalid_data(format!("Missing lambda interface type for {name}")))?;
    let info = LambdaInformation {
        method_name: dynamic.elementname.clone(),
        method_descriptor: method_descriptor.as_utf8_lossy().clone(),
        content_class_name,
        content_method_name: handle.elementname.clone(),
        content_method_descriptor: handle.descriptor.clone(),
        content_method_invocation_type: handle.index1,
        content_method_key: make_unique_key(&handle.elementname, &handle.descriptor).into(),
        is_method_reference,
        is_content_method_static: handle.index1 == CONSTANT_METHODHANDLE_REF_INVOKESTATIC,
    };
    Ok(ClassNode {
        class: Arc::clone(class),
        kind: ClassKind::Lambda,
        access: 0,
        simple_name: Some(name),
        enclosing_method: Some(make_unique_key(&enclosing.name, &enclosing.descriptor).into()),
        enclosing_classes: Default::default(),
        parent: Some(parent),
        nested: Vec::new(),
        anonymous_type: Some(VarType::from_signature_cl(lambda_class, true)),
        lambda: Some(info),
        wrapper: None,
        fields_to_vars: Default::default(),
        super_invocation: None,
        hidden_members: Default::default(),
    })
}

fn invalid_data(message: String) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}
