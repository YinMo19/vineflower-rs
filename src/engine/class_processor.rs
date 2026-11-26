// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Root-class preparation in `ClassesProcessor.processClass`, before wrapper initialization.

use std::io;
use std::sync::Arc;

use super::Cx;
use super::class_nodes::{ClassKind, ClassNodeId, ClassNodes, process_lambdas};
use super::class_writer::metadata::{module_info_to_java, package_info_to_java};
use super::import_collector::{ImportCollector, short_name, write_imports};
use crate::code::code_constants::{ACC_FINAL, ACC_MODULE, ACC_STATIC, ACC_SYNTHETIC, CLINIT_NAME};
use crate::structs::{StructClass, StructMember, StructMethod};
use crate::util::text_buffer::TextBuffer;

/// Start the root's import scope before discovering lambda classes. Nested
/// classes share this scope throughout method processing and source writing.
pub fn prepare_class(cx: &mut Cx, root: ClassNodeId) -> io::Result<()> {
    let node = &cx.class_nodes[root];
    if node.kind != ClassKind::Root {
        return Ok(());
    }
    cx.imports = ImportCollector::for_root(&cx.struct_context, &cx.class_nodes, node);
    cx.expression_ids = Default::default(); // DecompilerContext.startClass
    cx.source_mapper = Default::default();
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
    let mut order = Vec::new();
    append_wrapper_order(&cx.class_nodes, root, &mut order);
    cx.class_nodes.set_wrapper_order(root, order);
    Ok(())
}

/// Process the methods of a compilation unit with the given method pipeline.
pub fn process_class_methods(
    cx: &mut Cx,
    root: ClassNodeId,
    process: impl FnMut(
        &mut Cx,
        &StructClass,
        &Arc<StructMethod>,
    ) -> io::Result<Option<super::method_processor::ExpressionMethod>>,
) -> io::Result<()> {
    prepare_class(cx, root)?;
    super::class_wrapper::initialize_wrappers(cx, root, process)
}

/// Publish a compilation unit's methods through the complete built-in Java pipeline.
pub fn initialize_java_wrappers(cx: &mut Cx, root: ClassNodeId) -> io::Result<()> {
    process_class_methods(cx, root, super::method_processor::code_to_java)
}

/// Run the built-in Java processing for a root class and its nested classes.
pub fn process_class(cx: &mut Cx, root: ClassNodeId) -> io::Result<()> {
    if cx.class_nodes[root].kind != ClassKind::Root {
        return Ok(());
    }
    initialize_java_wrappers(cx, root)?;
    if cx.class_nodes[root].wrapper.is_some() {
        super::nested::process_class(cx, root)?;
        super::nested::propagate_member_access(cx, root)?;
    }
    Ok(())
}

/// Write a prepared package-info or module-info root, returning whether it
/// was handled by the metadata writer.
pub fn write_metadata(
    cx: &mut Cx,
    class: &StructClass,
    buffer: &mut TextBuffer,
) -> io::Result<bool> {
    let Some(root) = cx.class_nodes.id(&class.qualified_name) else {
        return Ok(false);
    };
    let node = &cx.class_nodes[root];
    if node.kind != ClassKind::Root {
        return Ok(false);
    }
    let result = if class.is_synthetic() && node.simple_name.as_deref() == Some("package-info") {
        package_info_to_java(cx, class, buffer).map(|()| write_imports(cx, buffer, false))
    } else if class.has_modifier(ACC_MODULE)
        && let Some(module) = &class.attributes.module
    {
        let mut body = TextBuffer::new(cx);
        module_info_to_java(cx, class, module, &mut body).map(|()| {
            write_imports(cx, buffer, true);
            buffer.append_buffer(&body);
        })
    } else {
        return Ok(false);
    };
    release_root(cx, root);
    result.map(|()| true)
}

/// Write a complete prepared compilation unit with imports, line wrapping
/// and source mappings, then release its root wrapper.
pub fn write_class(cx: &mut Cx, class: &StructClass, output: &mut TextBuffer) -> io::Result<()> {
    let root = cx.class_nodes.id(&class.qualified_name).ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidInput,
            "Class is not registered in this compilation group",
        )
    })?;
    if cx.class_nodes[root].kind != ClassKind::Root || write_metadata(cx, class, output)? {
        return Ok(());
    }
    let result = (|| {
        let mut body = TextBuffer::new(cx);
        super::class_writer::write_class(cx, root, &mut body, 0)?;
        body.reformat();
        for ((owner, key), mut tracer) in body.get_tracers() {
            let Some(key) = key else { continue };
            if let Some(owner_class) = cx.classes().get_class(&owner)
                && let Some(method) = owner_class.get_method_by_key(&key)
            {
                tracer.set_line_number_table(method.attributes.line_number_table.clone());
                cx.source_mapper.add_tracer(&owner, &key, &mut tracer);
            }
        }
        if let Some((package, _)) = class.qualified_name.rsplit_once('/') {
            output
                .append("package ")
                .append(&package.replace('/', "."))
                .append_char(';')
                .append_line_separator()
                .append_line_separator();
        }
        write_imports(cx, output, true);
        let header_lines = output.count_lines();
        output.append_buffer(&body);
        if cx.options.bytecode_source_mapping {
            cx.source_mapper.add_total_offset(header_lines);
            if cx.options.dump_original_lines {
                output.dump_original_line_numbers(&cx.source_mapper.original_lines_mapping());
            }
            if cx.options.unit_test_mode {
                output.append_line_separator();
                cx.source_mapper.dump_mapping(output, true);
            }
        }
        Ok(())
    })();
    release_root(cx, root);
    result
}

fn release_root(cx: &mut Cx, root: ClassNodeId) {
    let node = &mut cx.class_nodes[root];
    node.wrapper = None;
    // Method bytecode is owned by its Rust processing scope. Nested wrappers
    // remain available to constructor calls in other compilation units.
    for method in &node.class.methods {
        method.clear_variable_namer();
    }
}

fn append_wrapper_order(classes: &ClassNodes, id: ClassNodeId, order: &mut Vec<ClassNodeId>) {
    let node = &classes[id];
    if node.kind == ClassKind::Lambda {
        return;
    }

    let (early, later): (Vec<_>, Vec<_>) = node
        .nested
        .iter()
        .copied()
        .partition(|&child| should_init_early(&classes[child].class));
    for child in early {
        append_wrapper_order(classes, child, order);
    }
    order.push(id);
    for child in later {
        append_wrapper_order(classes, child, order);
    }
}

/// Synthetic holders for switch maps and assertion fields initialize before their owner.
fn should_init_early(class: &StructClass) -> bool {
    class.has_modifier(ACC_SYNTHETIC)
        && matches!(&class.methods[..], [method] if method.name == CLINIT_NAME)
        && class.fields.iter().all(|field| {
            matches!(field.descriptor.as_str(), "[I" | "Z")
                && field.has_modifier(ACC_STATIC | ACC_FINAL | ACC_SYNTHETIC)
        })
}
