// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Native Java source writing after class and method processing.

pub(super) mod annotations;
pub(super) mod metadata;
pub(crate) mod type_annotations;

mod class_references14;
mod declaration;
mod enums;
mod initializers;
pub mod javadoc;
mod late_methods;
mod record_components;
mod records;

pub use declaration::write_class_definition;

use super::{
    Cx,
    class_nodes::{ClassKind, ClassNodeId},
    class_wrapper::{MethodSlot, catch_method_failure},
};
use crate::code::code_constants::ACC_ENUM;
use crate::structs::StructMember;
use std::io;

/// Run the built-in Java passes at ClassWriter.invokeProcessors. The class and
/// its nested methods must already have gone through ClassesProcessor.processClass.
pub fn prepare_class_for_writing(cx: &mut Cx, node: ClassNodeId) -> io::Result<()> {
    if cx.class_nodes[node].wrapper.is_none() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "Class has not been processed yet",
        ));
    }
    cx.with_class_node(node, |cx| catch_method_failure(|| prepare(cx, node)))
}

fn prepare(cx: &mut Cx, node: ClassNodeId) -> io::Result<()> {
    late_methods::process(cx, node)?;
    initializers::extract(cx, node)?;
    initializers::hide_initializers(cx, node);
    let class = &cx.class_nodes[node];
    if class.kind == ClassKind::Root
        && class.class.version.has_14_class_references()
        && cx.options.decompile_java4
    {
        class_references14::process(cx, node)?;
    }
    if cx.class_nodes[node].class.has_modifier(ACC_ENUM) && cx.options.decompile_enums {
        enums::clear_enum(cx, node)?;
    }
    for index in 0..cx.class_nodes[node].class.methods.len() {
        let slot = MethodSlot { node, index };
        late_methods::reset_method(cx, slot);
        records::fixup_canonical_constructor(cx, slot);
        let method = slot.get(cx);
        if let Some(root) = method.root() {
            let (variables, method) = (method.variables, method.method.clone());
            crate::decompiler::vars::processor::rerun_clashing(cx, root, variables, &method)?;
        }
    }
    Ok(())
}
