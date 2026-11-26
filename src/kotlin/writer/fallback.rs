// SPDX-License-Identifier: Apache-2.0

//! KotlinWriter's field and method writers for declarations without Kotlin bindings.

use std::{io, sync::Arc};

use arcstr::ArcStr;

use crate::{
    code::code_constants::*,
    decompiler::{
        expr_processor::get_cast_type_name,
        exps::{
            ExprKind, WriteFlags, literal,
            write::{
                self,
                casts::{CastOptions, append_casted},
            },
        },
    },
    engine::{
        Cx,
        class_nodes::{ClassKind, ClassNodeId},
        class_writer::{
            append_deprecation, append_wrapper_comments,
            comments::{self, RenameKind},
            declared_exceptions,
            javadoc::{self, JavadocStyle},
            method_generic_signature, with_method_for_writing,
        },
    },
    kotlin::{
        members::{self, ClassElement},
        types::kotlin_type,
    },
    structs::{StructClass, StructField, StructMember, StructMethod, attr::TypeAnnotationData},
    types::{GenericMethodDescriptor, MethodDescriptor, VarType},
    util::{interpreter_util::make_unique_key, text_buffer::TextBuffer},
};

use super::{
    annotations,
    modifiers::{self, FIELD_ALLOWED, FIELD_EXCLUDED},
};

mod parameters;

const ACCESSIBILITY: i32 = ACC_PUBLIC | ACC_PROTECTED | ACC_PRIVATE;

pub fn write_field(
    cx: &mut Cx,
    node: ClassNodeId,
    field: &StructField,
    buffer: &mut TextBuffer,
    indent: i32,
) -> io::Result<()> {
    let class = Arc::clone(&cx.class_nodes[node].class);
    let interface = class.has_modifier(ACC_INTERFACE);
    let is_enum = cx.options.decompile_enums && field.has_modifier(ACC_ENUM);
    append_deprecation(buffer, &field.attributes, indent);
    let name = member_name(
        cx,
        &class,
        &field.name,
        &field.descriptor,
        buffer,
        RenameKind::Field,
        indent,
    )?;
    if let Some(doc) = cx
        .javadoc
        .as_ref()
        .and_then(|provider| provider.field_doc(&class, field))
    {
        javadoc::append(buffer, JavadocStyle::Html, &doc, indent);
    }
    annotations::append(cx, buffer, indent, field, TypeAnnotationData::FIELD)?;
    annotations::append_jvm(
        buffer,
        indent,
        field,
        interface,
        is_in_file(cx, &class),
        &class.pool,
        TypeAnnotationData::FIELD,
    )?;

    buffer.append_indent(indent);
    if field.access_flags & (ACC_FINAL | ACC_STATIC | ACC_PRIVATE) == 0 {
        buffer.append("open ");
    }
    if !is_enum {
        modifiers::append_modifiers(
            buffer,
            field.access_flags,
            FIELD_ALLOWED,
            interface,
            FIELD_EXCLUDED,
        );
    }
    let erased = VarType::from_signature(&field.descriptor);
    let ty = field.verified_type(cx, &class, &erased);
    if !is_enum {
        buffer.append(&get_cast_type_name(cx, &ty)).append_char(' ');
    }
    buffer.append(&name);

    let wrapper = cx.class_nodes[node]
        .wrapper
        .as_ref()
        .ok_or_else(|| invalid("No Kotlin field initializer wrapper"))?;
    let initializers = if field.has_modifier(ACC_STATIC) {
        &wrapper.static_field_initializers
    } else {
        &wrapper.dynamic_field_initializers
    };
    if let Some(&expr) = initializers.get_with_key(&make_unique_key(&field.name, &field.descriptor))
    {
        if is_enum && matches!(cx.ir[expr].kind, ExprKind::New { .. }) {
            cx.ir[expr].write_flags.insert(WriteFlags::ENUM_CONST);
            buffer.append_buffer(&write::to_java(cx, expr, indent)?);
        } else {
            buffer.append(" = ");
            literal::adjust_const_type(&mut cx.ir, expr, &erased);
            append_casted(cx, expr, &ty, buffer, indent, CastOptions::default())?;
        }
    } else if field.has_modifier(ACC_FINAL | ACC_STATIC)
        && let Some(attribute) = &field.attributes.constant_value
    {
        let constant = class
            .pool
            .get_primitive_constant(attribute.index)
            .ok_or_else(|| invalid("Missing Kotlin field constant value"))?;
        cx.expression_ids.next();
        buffer.append(" = ").append_buffer(&literal::render(
            cx,
            &erased,
            &constant.value,
            None,
            false,
        )?);
    }
    if !is_enum {
        buffer.append_char(';').append_line_separator();
    }
    Ok(())
}

pub fn write_method(
    cx: &mut Cx,
    node: ClassNodeId,
    index: usize,
    method: &StructMethod,
    buffer: &mut TextBuffer,
    indent: i32,
) -> io::Result<bool> {
    with_method_for_writing(cx, node, index, |cx| {
        write_scoped_method(cx, node, index, method, buffer, indent)
    })
}

fn write_scoped_method(
    cx: &mut Cx,
    node: ClassNodeId,
    index: usize,
    method: &StructMethod,
    buffer: &mut TextBuffer,
    indent: i32,
) -> io::Result<bool> {
    let slot = cx
        .current_method_wrapper
        .expect("Kotlin method writer entered a wrapper");
    let class = Arc::clone(&cx.class_nodes[node].class);
    let descriptor = MethodDescriptor::parse_descriptor(&method.descriptor);
    if let Some(signature) = method_generic_signature(cx, node, method, &descriptor) {
        descriptor.add_generic_descriptor(signature);
    }
    let interface = class.has_modifier(ACC_INTERFACE);
    let is_annotation = class.has_modifier(ACC_ANNOTATION);
    let is_enum = cx.options.decompile_enums && class.has_modifier(ACC_ENUM);
    let mut flags = method.access_flags;
    if flags & ACC_NATIVE != 0 {
        flags &= !ACC_STRICT;
    }
    if method.name == CLINIT_NAME {
        flags &= ACC_STATIC;
    }

    append_deprecation(buffer, &method.attributes, indent);
    let name = member_name(
        cx,
        &class,
        &method.name,
        &method.descriptor,
        buffer,
        RenameKind::Method,
        indent,
    )?;
    if flags & ACC_BRIDGE != 0 {
        comments::append_comment(buffer, "bridge methodSupplier", indent);
    }
    append_wrapper_comments(cx, slot, buffer, indent);
    if let Some(doc) = cx
        .javadoc
        .as_ref()
        .and_then(|provider| provider.method_doc(&class, method))
    {
        javadoc::append(buffer, JavadocStyle::Html, &doc, indent);
    }
    annotations::append(
        cx,
        buffer,
        indent,
        method,
        TypeAnnotationData::METHOD_RETURN_TYPE,
    )?;
    annotations::append_jvm(
        buffer,
        indent,
        method,
        interface,
        is_in_file(cx, &class),
        &class.pool,
        TypeAnnotationData::METHOD_RETURN_TYPE,
    )?;
    buffer.append_indent(indent);

    let class_init = name == CLINIT_NAME;
    let anonymous_init = name == INIT_NAME && cx.class_nodes[node].kind == ClassKind::Anonymous;
    let named_init = name == INIT_NAME && !anonymous_init;
    let name = if named_init {
        cx.class_nodes[node]
            .simple_name
            .clone()
            .ok_or_else(|| invalid("Kotlin constructor has no class name"))?
    } else {
        name
    };
    let overrides = !matches!(method.name.as_str(), INIT_NAME | CLINIT_NAME)
        && method.access_flags & (ACC_STATIC | ACC_PRIVATE) == 0
        && members::search_for_method(cx, &class, &method.name, &descriptor);
    if overrides {
        buffer.append("override ");
        if method.has_modifier(ACC_ABSTRACT) {
            buffer.append("abstract ");
        }
        if method.has_modifier(ACC_FINAL) {
            buffer.append("final ");
        }
    } else if method.access_flags & (ACC_FINAL | ACC_PRIVATE | ACC_STATIC) == 0
        && !interface
        && !is_annotation
        && !is_enum
        && !class.has_modifier(ACC_FINAL)
    {
        buffer.append(if method.has_modifier(ACC_ABSTRACT) {
            "abstract "
        } else {
            "open "
        });
    }
    if !anonymous_init {
        buffer.append("fun ");
    }

    let signature = verified_method_signature(cx, node, &class, method, &descriptor, named_init)?;
    let mut parameter_count = 0;
    if !class_init && !anonymous_init {
        parameter_count = parameters::append(
            cx,
            buffer,
            parameters::Header {
                method,
                name: &name,
                descriptor: &descriptor,
                signature: signature.as_deref(),
                flags,
                is_interface: interface,
                enum_constructor: is_enum && named_init,
            },
            indent,
        )?;
        let ret = signature
            .as_ref()
            .map_or(&descriptor.ret, |signature| &signature.return_type);
        if !named_init && !ret.higher_equal_in_lattice_than(cx, &VarType::VARTYPE_VOID) {
            buffer.append(": ");
            let nullable = annotations::is_nullable(method);
            let name = kotlin_type(cx, Some(ret), true)?;
            append_kotlin_type(buffer, ret, &name, nullable, nullable);
        }
    }
    if flags & (ACC_ABSTRACT | ACC_NATIVE) != 0 {
        buffer.append_line_separator();
        return Ok(true);
    }
    if !class_init && !anonymous_init {
        buffer.append_char(' ');
    }
    let hide_if_init = class_init
        || anonymous_init
        || hide_constructor(cx, node, &class, named_init, parameter_count, flags);
    super::write_method_body(cx, node, index, buffer, indent, hide_if_init)
}

fn verified_method_signature(
    cx: &Cx,
    node: ClassNodeId,
    class: &StructClass,
    method: &StructMethod,
    descriptor: &MethodDescriptor,
    named_init: bool,
) -> io::Result<Option<Arc<GenericMethodDescriptor>>> {
    let Some(signature) = method.shared_signature() else {
        return Ok(None);
    };
    let skip = usize::from(cx.class_nodes[node].access & ACC_ENUM != 0 && named_init) * 2;
    let params = descriptor
        .params
        .get(skip..)
        .ok_or_else(|| invalid("Kotlin enum constructor has no name and ordinal parameters"))?;
    let exceptions = declared_exceptions(class, method);
    let raw = signature.get();
    if raw.parameter_types.len() > params.len() || raw.exception_types.len() > exceptions.len() {
        return Err(invalid(
            "Kotlin generic method signature exceeds its descriptor",
        ));
    }
    let checker = if let Some(sig) = class
        .signature()
        .filter(|_| !method.has_modifier(ACC_STATIC))
    {
        let mut checker = sig.get_checker();
        let mut parent = cx.class_nodes[node].parent;
        while let Some(id) = parent {
            if let Some(sig) = cx.class_nodes[id].class.signature() {
                checker = checker.copy_with_parent(&sig.get_checker());
            }
            parent = cx.class_nodes[id].parent;
        }
        Some(checker)
    } else {
        None
    };
    signature.update(|signature| {
        signature.verify_types(cx, checker.as_ref(), params, &descriptor.ret, &exceptions)
    });
    Ok(Some(signature.get()))
}

fn hide_constructor(
    cx: &Cx,
    node: ClassNodeId,
    class: &StructClass,
    init: bool,
    parameter_count: usize,
    flags: i32,
) -> bool {
    if !init || parameter_count > 0 || !cx.options.hide_default_constructor {
        return false;
    }
    let node = &cx.class_nodes[node];
    let class_access = if node.kind == ClassKind::Root {
        class.access_flags
    } else {
        node.access
    };
    let is_enum = class.has_modifier(ACC_ENUM) && cx.options.decompile_enums;
    if !is_enum && class_access & ACCESSIBILITY != flags & ACCESSIBILITY {
        return false;
    }
    match cx.kotlin_members() {
        Some(members) => members
            .methods(class)
            .filter(|method| method.name == INIT_NAME)
            .nth(1)
            .is_none(),
        None => class
            .methods
            .iter()
            .filter(|method| method.name == INIT_NAME)
            .nth(1)
            .is_none(),
    }
}

fn member_name(
    cx: &mut Cx,
    class: &StructClass,
    name: &ArcStr,
    descriptor: &str,
    buffer: &mut TextBuffer,
    kind: RenameKind,
    indent: i32,
) -> io::Result<ArcStr> {
    let Some(interceptor) = &cx.pool_interceptor else {
        return Ok(name.clone());
    };
    let mut name = name.clone();
    let key = format!("{} {name} {descriptor}", class.qualified_name);
    if let Some(renamed) = interceptor.get_name(&key) {
        name = renamed
            .split(' ')
            .nth(1)
            .ok_or_else(|| invalid("Invalid renamed Kotlin member"))?
            .into();
    }
    let old = interceptor
        .get_old_name(&format!("{} {name} {descriptor}", class.qualified_name))
        .map(str::to_owned);
    comments::append_rename_comment(cx, buffer, old.as_deref(), kind, indent)?;
    Ok(name)
}

fn is_in_file(cx: &Cx, class: &StructClass) -> bool {
    matches!(
        cx.kotlin_members().and_then(|members| members.class(class)),
        Some(ClassElement::File(_))
    )
}

fn append_kotlin_type(
    buffer: &mut TextBuffer,
    ty: &VarType,
    type_name: &str,
    parenthesize_function: bool,
    nullable: bool,
) {
    let enclosed = parenthesize_function
        && ty
            .value
            .as_ref()
            .is_some_and(|name| name.starts_with("kotlin/jvm/functions/Function"));
    if enclosed {
        buffer.append_char('(');
    }
    buffer.append(type_name);
    if enclosed {
        buffer.append_char(')');
    }
    if nullable {
        buffer.append_char('?');
    }
}

fn invalid(reason: &str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}
