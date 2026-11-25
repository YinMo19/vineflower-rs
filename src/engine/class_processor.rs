// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Root-class preparation in `ClassesProcessor.processClass`, before wrapper initialization.

use std::io;

use super::Cx;
use super::class_nodes::{ClassKind, ClassNodeId, process_lambdas};
use super::import_collector::{ImportCollector, short_name};
use crate::code::code_constants::ACC_MODULE;
use crate::structs::StructMember;

/// Start the root's import scope before discovering lambda classes. Nested
/// classes share this scope throughout method processing and source writing.
pub fn prepare_class(cx: &mut Cx, root: ClassNodeId) -> io::Result<()> {
    let node = &cx.class_nodes[root];
    if node.kind != ClassKind::Root {
        return Ok(());
    }
    cx.imports = ImportCollector::for_root(&cx.struct_context, &cx.class_nodes, node);
    let package_info =
        node.class.is_synthetic() && node.simple_name.as_deref() == Some("package-info");
    let module_info = node.class.has_modifier(ACC_MODULE) && node.class.attributes.module.is_some();
    if package_info || module_info {
        return Ok(());
    }
    process_lambdas(&mut cx.class_nodes, root)?;
    let mut pending = vec![root];
    while let Some(id) = pending.pop() {
        let node = &cx.class_nodes[id];
        pending.extend(node.nested.iter().rev().copied());
        if let Some(simple) = node.simple_name.as_ref().filter(|s| !s.is_empty()) {
            let name = if node.kind == ClassKind::Root {
                &node.class.qualified_name
            } else {
                simple
            };
            let name = name.clone();
            short_name(cx, &name, false);
        }
    }
    Ok(())
}
