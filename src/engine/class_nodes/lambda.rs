// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Discover `LambdaMetafactory` call sites and attach their class nodes.

use std::{
    any::Any,
    io,
    panic::{AssertUnwindSafe, catch_unwind, resume_unwind},
    sync::Arc,
};

use arcstr::ArcStr;
use rustc_hash::FxHashMap;

use super::{ClassKind, ClassNode, ClassNodeId, ClassNodes, LambdaInformation};
use crate::code::code_constants::{
    CONSTANT_INVOKEDYNAMIC, CONSTANT_METHODHANDLE, CONSTANT_METHODHANDLE_REF_INVOKESTATIC,
    CONSTANT_METHODTYPE, OPC_INVOKEDYNAMIC,
};
use crate::structs::attr::StructBootstrapMethodsAttribute;
use crate::structs::consts::{ConstantValue, LinkConstant, PooledConstant, PrimitiveConstant};
use crate::structs::struct_member::StructMember;
use crate::structs::{StructClass, StructMethod};
use crate::types::{MethodDescriptor, VarType};
use crate::util::interpreter_util::make_unique_key;

/// `LambdaProcessor.processClass`, before the class wrappers process methods.
pub fn process_lambdas(nodes: &mut ClassNodes, root: ClassNodeId) -> io::Result<()> {
    LambdaScan::default().publish(nodes, root)
}

/// The immutable bytecode discoveries for one root. Class identity lets
/// repeated visits and newly linked lambda nodes reuse the same discoveries
/// while publishing a fresh node for each occurrence in the live tree.
#[derive(Default)]
pub(crate) struct LambdaScan(FxHashMap<usize, Option<ClassLambdaScan>>);

struct ClassLambdaScan {
    sites: Vec<LambdaSite>,
    failure: Option<ScanFailure>,
}

enum ScanFailure {
    Io(io::Error),
    Panic(Box<dyn Any + Send>),
}

struct LambdaSite {
    name: ArcStr,
    enclosing_method: ArcStr,
    anonymous_type: VarType,
    information: LambdaInformation,
}

impl LambdaScan {
    pub(crate) fn for_root(nodes: &ClassNodes, root: ClassNodeId) -> Self {
        let mut scan = Self::default();
        scan.scan_postorder(nodes, root);
        scan
    }

    fn scan_postorder(&mut self, nodes: &ClassNodes, node: ClassNodeId) -> bool {
        for &child in &nodes[node].nested {
            if !self.scan_postorder(nodes, child) {
                return false;
            }
        }
        self.class_scan(&nodes[node].class)
            .as_ref()
            .is_none_or(|scan| scan.failure.is_none())
    }

    fn class_scan(&mut self, class: &Arc<StructClass>) -> &mut Option<ClassLambdaScan> {
        self.0
            .entry(Arc::as_ptr(class) as usize)
            .or_insert_with(|| scan_class(class))
    }

    pub(crate) fn publish(mut self, nodes: &mut ClassNodes, root: ClassNodeId) -> io::Result<()> {
        self.publish_subtree(nodes, root)
    }

    fn publish_subtree(&mut self, nodes: &mut ClassNodes, root: ClassNodeId) -> io::Result<()> {
        // Visit the live tree: publishing a descendant can change lambda links.
        for child in nodes[root].nested.clone() {
            self.publish_subtree(nodes, child)?;
        }

        let class = Arc::clone(&nodes[root].class);
        let Some(scan) = self.class_scan(&class) else {
            return Ok(());
        };
        let mut lambda_by_content_method = FxHashMap::default();
        for site in &scan.sites {
            // A repeated synthetic name resolves to the last call site while
            // earlier nodes survive.
            let child = nodes.insert(site.name.clone(), site.node(&class, root));
            nodes[root].nested.push(child);
            if !site.information.is_method_reference {
                lambda_by_content_method.insert(
                    site.information.content_method_key.clone(),
                    site.name.clone(),
                );
            }
        }
        match scan.failure.take() {
            Some(ScanFailure::Io(error)) => return Err(error),
            Some(ScanFailure::Panic(payload)) => resume_unwind(payload),
            None => {}
        }
        link_lambdas(nodes, root, &lambda_by_content_method)
    }
}

fn scan_class(class: &StructClass) -> Option<ClassLambdaScan> {
    if !class.version.has_lambdas() {
        return None;
    }
    let bootstrap = class.attributes.bootstrap_methods.as_ref()?;
    let lambda_methods: Vec<_> = bootstrap
        .method_refs
        .iter()
        .map(is_lambda_bootstrap)
        .collect();
    if !lambda_methods.iter().any(|&is_lambda| is_lambda) {
        return None;
    }

    let mut sites = Vec::new();
    let result = catch_unwind(AssertUnwindSafe(|| {
        scan_sites(class, bootstrap, &lambda_methods, &mut sites)
    }));
    let failure = match result {
        Ok(Ok(())) => None,
        Ok(Err(error)) => Some(ScanFailure::Io(error)),
        Err(payload) => Some(ScanFailure::Panic(payload)),
    };
    Some(ClassLambdaScan { sites, failure })
}

fn scan_sites(
    class: &StructClass,
    bootstrap: &StructBootstrapMethodsAttribute,
    lambda_methods: &[bool],
    sites: &mut Vec<LambdaSite>,
) -> io::Result<()> {
    for method in &class.methods {
        let Some(seq) = method.expand_data(class)? else {
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
            sites.push(LambdaSite::new(class, method, name, dynamic, args)?);
        }
    }
    Ok(())
}

fn link_lambdas(
    nodes: &mut ClassNodes,
    root: ClassNodeId,
    lambda_by_content_method: &FxHashMap<ArcStr, ArcStr>,
) -> io::Result<()> {
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

impl LambdaSite {
    fn new(
        class: &StructClass,
        enclosing: &StructMethod,
        name: ArcStr,
        dynamic: &LinkConstant,
        args: &[Option<PooledConstant>],
    ) -> io::Result<Self> {
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
        Ok(Self {
            name,
            enclosing_method: make_unique_key(&enclosing.name, &enclosing.descriptor).into(),
            anonymous_type: VarType::from_signature_cl(lambda_class, true),
            information: info,
        })
    }

    fn node(&self, class: &Arc<StructClass>, parent: ClassNodeId) -> ClassNode {
        ClassNode {
            class: Arc::clone(class),
            kind: ClassKind::Lambda,
            access: 0,
            simple_name: Some(self.name.clone()),
            enclosing_method: Some(self.enclosing_method.clone()),
            enclosing_classes: Default::default(),
            parent: Some(parent),
            nested: Vec::new(),
            anonymous_type: Some(self.anonymous_type.clone()),
            lambda: Some(self.information.clone()),
            wrapper: None,
            fields_to_vars: Default::default(),
            super_invocation: None,
            hidden_members: Default::default(),
        }
    }
}

fn invalid_data(message: String) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}
