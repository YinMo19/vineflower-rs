//! ClassWriter.writeMethod, from declaration through the body and hiding decision.

use std::{io, sync::Arc};

use super::annotations::{append_annotations, render_element};
use super::comments::{RenameKind, append_comment, append_rename_comment, error_comment};
use super::declaration::{append_deprecation, append_modifiers};
use super::method_errors::dump_error;
use super::method_parameters::{self, ParameterHeader};
use super::type_annotations::{TypeAnnotations, append_type_parameters};
use super::{javadoc, records, with_method_for_writing};
use crate::code::code_constants::{
    ACC_ABSTRACT, ACC_ANNOTATION, ACC_BRIDGE, ACC_ENUM, ACC_FINAL, ACC_INTERFACE, ACC_NATIVE,
    ACC_PRIVATE, ACC_PROTECTED, ACC_PUBLIC, ACC_STATIC, ACC_STRICT, ACC_SYNCHRONIZED, CLINIT_NAME,
    INIT_NAME,
};
use crate::decompiler::exps::literal::add_offsets;
use crate::decompiler::stats::{StatementKind, write};
use crate::engine::Cx;
use crate::engine::class_nodes::{ClassKind, ClassNodeId};
use crate::engine::class_wrapper::{MethodSlot, catch_method_failure};
use crate::structs::{StructClass, StructMember, StructMethod, attr::TypeAnnotationData};
use crate::types::{
    GenericMethodDescriptor, GenericsChecker, MethodDescriptor, SharedSignature, VarType,
};
use crate::util::{
    interpreter_util::make_unique_key, text_buffer::TextBuffer, text_util::to_valid_java_identifier,
};

const ACCESSIBILITY: i32 = ACC_PUBLIC | ACC_PROTECTED | ACC_PRIVATE;
const METHOD_ALLOWED: i32 = ACCESSIBILITY
    | ACC_ABSTRACT
    | ACC_STATIC
    | ACC_FINAL
    | ACC_SYNCHRONIZED
    | ACC_NATIVE
    | ACC_STRICT;

pub(super) fn write_method(
    cx: &mut Cx,
    node: ClassNodeId,
    index: usize,
    buffer: &mut TextBuffer,
    indent: i32,
) -> io::Result<bool> {
    with_method_for_writing(cx, node, index, |cx| {
        write_in_method(cx, node, buffer, indent)
    })
}

fn write_in_method(
    cx: &mut Cx,
    node: ClassNodeId,
    buffer: &mut TextBuffer,
    indent: i32,
) -> io::Result<bool> {
    let slot = cx
        .current_method_wrapper
        .expect("Method writer requires a wrapper");
    let class = Arc::clone(&cx.class_nodes[slot.node].class);
    let method = Arc::clone(&slot.get(cx).method);
    let descriptor = MethodDescriptor::parse_descriptor(&method.descriptor);
    let generic = signature(cx, node, &method, &descriptor);
    if let Some(signature) = &generic {
        descriptor.add_generic_descriptor(signature.clone());
    }

    let interface = class.has_modifier(ACC_INTERFACE);
    let is_enum = cx.options.decompile_enums && class.has_modifier(ACC_ENUM);
    let mut flags = method.access_flags;
    if flags & ACC_NATIVE != 0 {
        flags &= !ACC_STRICT;
    }
    if method.name == CLINIT_NAME {
        flags &= ACC_STATIC;
    }

    append_deprecation(buffer, &method.attributes, indent);
    let mut method_name = method.name.clone();
    if let Some(interceptor) = &cx.pool_interceptor
        && let Some(renamed) = interceptor.get_name(&format!(
            "{} {} {}",
            class.qualified_name, method.name, method.descriptor
        ))
    {
        method_name = renamed
            .split(' ')
            .nth(1)
            .ok_or_else(|| invalid("Invalid renamed method"))?
            .into();
    }
    let old = cx
        .pool_interceptor
        .as_ref()
        .and_then(|interceptor| {
            interceptor.get_old_name(&format!(
                "{} {} {}",
                class.qualified_name, method_name, method.descriptor
            ))
        })
        .map(str::to_owned);
    append_rename_comment(cx, buffer, old.as_deref(), RenameKind::Method, indent)?;
    if method.is_synthetic() {
        append_comment(buffer, "synthetic method", indent);
    }
    if flags & ACC_BRIDGE != 0 {
        append_comment(buffer, "bridge method", indent);
    }
    append_wrapper_comments(cx, slot, buffer, indent);
    if let Some(provider) = &cx.javadoc {
        let style = provider.method_style(&class, &method);
        if let Some(doc) = provider.method_doc(&class, &method) {
            javadoc::append(buffer, style, &doc, indent);
        }
    }
    let written = append_annotations(
        cx,
        buffer,
        &method.attributes,
        indent,
        TypeAnnotationData::METHOD_RETURN_TYPE,
    )?;
    if should_append_override(cx, &class, &method, &descriptor) {
        buffer
            .append_indent(indent)
            .append("@Override")
            .append_line_separator();
    }

    buffer.append_indent(indent);
    let class_init = method_name == CLINIT_NAME;
    let constructor = method_name == INIT_NAME;
    let anonymous_init = constructor && cx.class_nodes[node].kind == ClassKind::Anonymous;
    let named_init = constructor && !anonymous_init;
    if constructor {
        if is_enum {
            flags &= !ACC_PRIVATE;
        }
        if named_init {
            method_name = cx.class_nodes[node]
                .simple_name
                .clone()
                .ok_or_else(|| invalid("Named constructor has no class name"))?;
        }
    }
    if !anonymous_init {
        let implicit_flags = if interface {
            ACC_ABSTRACT | ACC_PUBLIC
        } else {
            0
        };
        append_modifiers(buffer, flags & METHOD_ALLOWED & !implicit_flags);
    }
    if interface
        && !method.has_modifier(ACC_STATIC)
        && method.contains_code()
        && flags & ACC_PRIVATE == 0
    {
        buffer.append("default ");
    }

    let erased_exceptions = declared_exceptions(&class, &method);
    let generic = generic.map(|signature| {
        let params = verification_parameters(
            cx,
            slot,
            &descriptor,
            &signature.get(),
            named_init && class.has_modifier(ACC_ENUM),
        );
        let checker = generic_context(cx, node);
        signature.update(|signature| {
            signature.verify_types(
                cx,
                Some(&checker),
                &params,
                &descriptor.ret,
                &erased_exceptions,
            );
        });
        signature.get()
    });

    let mut param_count = 0;
    let mut throws = false;
    if !class_init && !anonymous_init {
        if let Some(sig) = &generic
            && !sig.type_parameters.is_empty()
        {
            append_type_parameters(cx, buffer, &sig.type_parameters, &sig.type_parameter_bounds);
            buffer.append_char(' ');
        }
        if !named_init {
            let ty = generic
                .as_ref()
                .map_or(&descriptor.ret, |sig| &sig.return_type);
            let mut paths = TypeAnnotations::for_target(
                &method.attributes,
                TypeAnnotationData::METHOD_RETURN_TYPE,
                -1,
            );
            if paths.is_empty() {
                buffer.append_cast_type_name(cx, ty);
            } else {
                buffer
                    .append_annotated_cast_type_name(cx, ty, &mut paths, &written, false, true)?;
            }
            buffer.append_char(' ');
        }
        let name = to_valid_java_identifier(method_name.as_str());
        buffer.append_method_with(
            &name,
            true,
            &class.qualified_name,
            &method.name,
            descriptor.clone(),
        );
        if name.as_ref() != method_name.as_str() {
            buffer
                .append("/* $VF was: ")
                .append(&method_name)
                .append(" */");
        }
        if !slot.get(cx).is_compact_record_constructor {
            param_count = method_parameters::append(
                cx,
                buffer,
                ParameterHeader {
                    method: &method,
                    class: &class,
                    descriptor: &descriptor,
                    generic: generic.as_deref(),
                    slot,
                    flags,
                    enum_constructor: named_init && is_enum,
                },
                indent,
            )?;
        }
        throws = append_throws(cx, buffer, &method, generic.as_deref(), &erased_exceptions);
    }

    if flags & (ACC_ABSTRACT | ACC_NATIVE) != 0 {
        if class.has_modifier(ACC_ANNOTATION)
            && let Some(default) = &method.attributes.annotation_default
        {
            buffer.append(" default ").append_buffer(&render_element(
                cx,
                &default.default_value.value,
                0,
            )?);
        }
        buffer.append_char(';').append_line_separator();
        return Ok(true);
    }
    if !class_init && !anonymous_init {
        buffer.append_char(' ');
    }
    buffer.append_char('{').append_line_separator();

    let mut hide = false;
    let wrapper = slot.get(cx);
    if wrapper.decompile_error().is_none()
        && let Some(root) = wrapper.root()
    {
        let formatted = catch_method_failure(|| {
            if records::is_hidden_record_method(cx, &class, &method, root) {
                return Ok(None);
            }
            let mut code = write::to_java(cx, root, indent + 1)?;
            let StatementKind::Root { dummy_exit, .. } = cx.ir[root].kind else {
                unreachable!()
            };
            let StatementKind::DummyExit { ref bytecode } = cx.ir[dummy_exit].kind else {
                unreachable!()
            };
            add_offsets(&mut code, bytecode.as_ref());
            Ok(Some(code))
        });
        match formatted {
            Ok(None) => hide = true,
            Ok(Some(code)) => {
                hide = code.length() == 0
                    && (class_init
                        || anonymous_init
                        || hide_constructor(
                            cx,
                            node,
                            &method,
                            named_init,
                            throws,
                            param_count,
                            flags,
                        ));
                let key = make_unique_key(&method.name, &method.descriptor);
                buffer.append_buffer_for(&code, Some(&class.qualified_name), Some(&key));
            }
            Err(error) if error.kind() == io::ErrorKind::Interrupted => return Err(error),
            Err(error) => {
                log::warn!(
                    "Method {} {} in class {} couldn't be written: {error}",
                    method.name,
                    method.descriptor,
                    class.qualified_name
                );
                slot.record_write_error(cx, error);
            }
        }
    }
    if slot.get(cx).decompile_error().is_some() {
        dump_error(cx, buffer, &class, slot.get(cx), indent + 1);
    }
    buffer
        .append_indent(indent)
        .append_char('}')
        .append_line_separator();
    Ok(!hide)
}

pub(crate) fn append_wrapper_comments(cx: &mut Cx, slot: MethodSlot, buffer: &mut TextBuffer, indent: i32) {
    let wrapper = slot.get(cx);
    if !((cx.options.decompiler_comments && wrapper.add_error_comment)
        || wrapper.comment_lines.is_some())
    {
        return;
    }
    if wrapper.add_error_comment {
        let options = Arc::clone(&cx.options);
        let wrapper = slot.get_mut(cx);
        for line in error_comment(&options.error_message) {
            wrapper.add_comment(line);
        }
    }
    if let Some(lines) = &slot.get(cx).comment_lines {
        for line in lines {
            buffer
                .append_indent(indent)
                .append("// ")
                .append(line)
                .append_line_separator();
        }
    }
}

fn should_append_override(
    cx: &Cx,
    class: &StructClass,
    method: &StructMethod,
    desc: &MethodDescriptor,
) -> bool {
    cx.options.override_annotation
        && method.bytecode_version.has_override()
        && !matches!(method.name.as_str(), INIT_NAME | CLINIT_NAME)
        && method.access_flags & (ACC_STATIC | ACC_PRIVATE) == 0
        && search_for_method(cx, class, &method.name, desc, false)
        && method
            .attributes
            .runtime_visible_annotations
            .as_ref()
            .is_none_or(|annotations| {
                !annotations
                    .annotations
                    .iter()
                    .any(|entry| entry.class_name == "java/lang/Override")
            })
}

fn search_for_method(
    cx: &Cx,
    class: &StructClass,
    name: &str,
    desc: &MethodDescriptor,
    search: bool,
) -> bool {
    search
        && class.methods.iter().any(|method| {
            method.name == name
                && method.descriptor == desc.as_str()
                && !method.has_modifier(ACC_STATIC)
        })
        || class
            .super_class
            .iter()
            .map(|parent| parent.get_string())
            .chain(&class.interface_names)
            .filter_map(|name| cx.classes().get_class(name))
            .any(|parent| search_for_method(cx, &parent, name, desc, true))
}

pub(crate) fn signature(
    cx: &Cx,
    node: ClassNodeId,
    method: &StructMethod,
    desc: &MethodDescriptor,
) -> Option<Arc<SharedSignature<GenericMethodDescriptor>>> {
    let signature = method.shared_signature()?.clone();
    let method_key = make_unique_key(&method.name, &method.descriptor);
    let wrapper = MethodSlot::by_key(cx, node, &method_key);
    let mask = wrapper.and_then(|slot| slot.get(cx).synthetic_parameters.as_deref());

    let mut actual = desc.params.len();
    if let Some(mask) = mask {
        actual = mask.iter().filter(|parameter| parameter.is_none()).count();
    } else if method.name == INIT_NAME
        && cx.class_nodes[node].kind != ClassKind::Anonymous
        && cx.options.decompile_enums
    {
        let name = &method.class_qualified_name;
        let original = cx
            .pool_interceptor
            .as_ref()
            .and_then(|pool| pool.get_old_name(name))
            .unwrap_or(name);
        if cx
            .classes()
            .get_class(original)
            .is_some_and(|class| class.has_modifier(ACC_ENUM))
        {
            actual = actual.saturating_sub(2);
        }
    }
    let parsed = signature.get();
    if actual == parsed.parameter_types.len() {
        return Some(signature);
    }

    let Some(mask) = mask.filter(|mask| mask.len() == parsed.parameter_types.len()) else {
        log::warn!(
            "Descriptor and signature parameter counts mismatch, assuming ok: {} {}{}",
            method.class_qualified_name,
            method.name,
            method.descriptor
        );
        return Some(signature);
    };
    log::warn!(
        "Descriptor and signature parameter counts mismatch, attempting to correct: {} {}{}",
        method.class_qualified_name,
        method.name,
        method.descriptor
    );
    let mut fixed = GenericMethodDescriptor::clone(&parsed);
    fixed.parameter_types = parsed
        .parameter_types
        .iter()
        .zip(mask)
        .filter(|(_, parameter)| parameter.is_none())
        .map(|(ty, _)| ty.clone())
        .collect();
    Some(SharedSignature::new(fixed))
}

fn verification_parameters(
    cx: &Cx,
    slot: MethodSlot,
    desc: &MethodDescriptor,
    signature: &GenericMethodDescriptor,
    enum_constructor: bool,
) -> Vec<VarType> {
    let start = usize::from(enum_constructor) * 2;
    let mut params: Vec<_> = desc.params.iter().skip(start).cloned().collect();
    if params.len() != signature.parameter_types.len()
        && let Some(mask) = &slot.get(cx).synthetic_parameters
    {
        let mut index = 0;
        params.retain(|_| {
            let visible = mask.get(index).is_none_or(Option::is_none);
            index += 1;
            visible
        });
    }
    params
}

fn generic_context(cx: &Cx, node: ClassNodeId) -> GenericsChecker {
    let mut checker = GenericsChecker::default();
    let mut current = Some(node);
    while let Some(id) = current {
        let node = &cx.class_nodes[id];
        if let (Some(key), Some(parent)) = (&node.enclosing_method, node.parent) {
            let parent = &cx.class_nodes[parent];
            if let Some(method) = parent.class.get_method_by_key(key) {
                if let Some(signature) = method.signature() {
                    checker = checker
                        .copy_with(&signature.type_parameters, &signature.type_parameter_bounds);
                }
                // A local or anonymous class in a lambda body is attached to the
                // declaring class. Lambda nodes already have their lexical parent.
                if matches!(node.kind, ClassKind::Local | ClassKind::Anonymous)
                    && method.is_synthetic()
                    && let Some(&body) = parent.nested.iter().find(|&&child| {
                        cx.class_nodes[child].lambda.as_ref().is_some_and(|info| {
                            !info.is_method_reference && info.content_method_key == *key
                        })
                    })
                {
                    current = Some(body);
                    continue;
                }
            }
        }
        if let Some(signature) = node.class.signature() {
            checker = checker.copy_with_parent(&signature.get_checker());
        }
        current = node.parent;
    }
    checker
}

pub(crate) fn declared_exceptions(class: &StructClass, method: &StructMethod) -> Vec<VarType> {
    method
        .attributes
        .exceptions
        .iter()
        .flat_map(|attribute| {
            (0..attribute.throws_exceptions.len()).map(|index| {
                VarType::from_signature_cl(&attribute.get_exc_classname(index, &class.pool), true)
            })
        })
        .collect()
}

fn append_throws(
    cx: &mut Cx,
    buffer: &mut TextBuffer,
    method: &StructMethod,
    generic: Option<&GenericMethodDescriptor>,
    erased: &[VarType],
) -> bool {
    let generic = generic
        .map(|sig| sig.exception_types.as_slice())
        .filter(|exceptions| !exceptions.is_empty());
    if method.attributes.exceptions.is_none() && generic.is_none() {
        return false;
    }
    buffer.append(" throws ");
    let exceptions = generic.unwrap_or(erased);
    let limit = method
        .attributes
        .exceptions
        .as_ref()
        .map_or(exceptions.len(), |attribute| {
            attribute.throws_exceptions.len()
        });
    for (i, exception) in exceptions.iter().take(limit).enumerate() {
        if i > 0 {
            buffer.append(", ");
        }
        buffer.append_cast_type_name(cx, exception);
    }
    true
}

fn hide_constructor(
    cx: &Cx,
    node: ClassNodeId,
    method: &StructMethod,
    constructor: bool,
    throws: bool,
    param_count: usize,
    flags: i32,
) -> bool {
    if !constructor || throws || param_count > 0 || !cx.options.hide_default_constructor {
        return false;
    }
    let node = &cx.class_nodes[node];
    let class = &node.class;
    let access = if node.kind == ClassKind::Root {
        class.access_flags
    } else {
        node.access
    };
    let is_enum = cx.options.decompile_enums && class.has_modifier(ACC_ENUM);
    let record = class.get_record_components().is_some();
    if !is_enum && !record && access & ACCESSIBILITY != flags & ACCESSIBILITY {
        return false;
    }
    if record {
        !records::has_annotations(method)
    } else {
        class
            .methods
            .iter()
            .filter(|method| method.name == INIT_NAME)
            .nth(1)
            .is_none()
    }
}

fn invalid(message: &str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}
