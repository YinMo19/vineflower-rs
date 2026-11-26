// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Native Java source writing after class and method processing.

pub(crate) mod annotations;
pub(super) mod metadata;
pub(crate) mod type_annotations;

mod class;
mod class_references14;
pub(crate) mod comments;
pub(crate) mod declaration;
mod enums;
mod fields;
mod initializers;
pub mod javadoc;
mod lambda;
mod late_methods;
mod method_errors;
pub(crate) use method_errors::{
    dump_method_error, exception_details, write_class_error, write_exception,
};
mod method_parameters;
mod methods;
mod record_components;
pub(crate) use records::is_hidden_record_method;
mod records;

pub use class::write_class;
pub use declaration::write_class_definition;
pub(crate) use declaration::append_deprecation;
pub(crate) use methods::{append_wrapper_comments, declared_exceptions, signature as method_generic_signature};
pub(crate) use lambda::write_lambda;

use super::{
    Cx,
    class_nodes::{ClassKind, ClassNodeId},
    class_wrapper::{MethodSlot, catch_method_failure},
};
use crate::code::code_constants::ACC_ENUM;
use crate::structs::StructMember;
use std::io;

/// Render within a declared method's ClassWriter context. Local classes and
/// lambda bodies can enter another method and then return to this one.
pub fn with_method_for_writing<T>(
    cx: &mut Cx,
    node: ClassNodeId,
    index: usize,
    write: impl FnOnce(&mut Cx) -> io::Result<T>,
) -> io::Result<T> {
    let owner = cx
        .class_nodes
        .wrapper_owner(node)
        .filter(|&owner| {
            cx.class_nodes[owner]
                .wrapper
                .as_ref()
                .is_some_and(|w| index < w.methods.len())
        })
        .ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::InvalidInput,
                "missing method wrapper for writing",
            )
        })?;
    let slot = MethodSlot { node: owner, index };
    cx.with_class_node(node, |cx| slot.with_current(cx, write))
}

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
    prepare_initializers_and_enums(cx, node)?;
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

/// The initializer, class-reference and enum passes shared by the Java and Kotlin writers.
pub(crate) fn prepare_initializers_and_enums(cx: &mut Cx, node: ClassNodeId) -> io::Result<()> {
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
    Ok(())
}
