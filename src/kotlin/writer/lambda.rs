//! Kotlin class-based and invokedynamic lambdas, and callable references.

use std::io;

use crate::decompiler::exps::{ExitType, ExprKind, literal};
use crate::decompiler::ir::{ExprId, StatId};
use crate::decompiler::stats::{StatementKind, stat_edge::EdgeType};
use crate::decompiler::vars::var_version_pair::VarVersionPair;
use crate::engine::{
    Cx,
    class_nodes::{ClassKind, ClassNodeId, LambdaInformation},
    class_wrapper::{MethodSlot, catch_method_failure},
    import_collector::get_short_name,
};
use crate::kotlin::{
    body::{self, KotlinExpr},
    members::{self, ClassElement, KFunction},
    types::kotlin_type,
};
use crate::types::{MethodDescriptor, VarType};
use crate::util::{
    interpreter_util::make_unique_key, java_str::JavaString, text_buffer::TextBuffer,
};

pub(super) fn write_lambda(
    cx: &mut Cx,
    node: ClassNodeId,
    buf: &mut TextBuffer,
    indent: i32,
    function: Option<&KFunction>,
) -> io::Result<()> {
    let Some(function) = function else {
        let node = &cx.class_nodes[node];
        log::warn!(
            "No Kotlin function information for lambda class {}",
            node.simple_name.as_deref().unwrap_or("null")
        );
        buf.append_char('{')
            .append_line_separator()
            .append_indent(indent + 1)
            .append("// $VF: Could not decompile lambda - root function was not found. Is this a suspend lambda?")
            .append_line_separator()
            .append_indent(indent)
            .append_char('}');
        return Ok(());
    };

    let owner = cx.class_nodes[node].class.qualified_name.clone();
    lambda_parameters(cx, buf, function, &owner, indent, true)?;
    let slot = function_slot(cx, node, function)?;
    super::write_code(cx, node, slot.index(), buf, indent + 1, false)?;
    if slot.get(cx).decompile_error().is_some() {
        super::dump_error(cx, node, slot.index(), buf, indent + 1);
    }
    buf.append_indent(indent).append_char('}');
    Ok(())
}

fn lambda_parameters(
    cx: &mut Cx,
    buf: &mut TextBuffer,
    function: &KFunction,
    owner: &str,
    indent: i32,
    include_types: bool,
) -> io::Result<()> {
    let method = &function.method;
    let descriptor = MethodDescriptor::parse_descriptor(&method.descriptor);
    let mut index = 0;
    buf.append_char('{');
    for parameter in &function.parameters {
        buf.append(if index > 0 { ", " } else { " " })
            .append_variable(
                &parameter.name,
                true,
                true,
                owner,
                &method.name,
                descriptor.clone(),
                index,
                if include_types {
                    &method.name
                } else {
                    &parameter.name
                },
            );
        if include_types {
            buf.append(": ");
            parameter.ty.write(cx, buf, indent + 1)?;
        }
        index += parameter.ty.jvm.stack_size;
    }
    if !function.parameters.is_empty() {
        buf.append(" ->");
    }
    buf.append_line_separator();
    Ok(())
}

pub(crate) fn field_expression(
    cx: &mut Cx,
    expr: ExprId,
    indent: i32,
) -> io::Result<Option<TextBuffer>> {
    let ExprKind::Field(field) = &cx.ir[expr].kind else {
        unreachable!("Expected a Kotlin field expression")
    };
    let Some(owner) = field.classname.clone().filter(|_| field.name == "INSTANCE") else {
        return Ok(None);
    };
    let Some(class) = cx.classes().get_class(&owner) else {
        return Ok(None);
    };
    members::parse_metadata_for(cx, &class);
    let element = cx
        .kotlin_members()
        .and_then(|members| members.class(&class))
        .cloned();
    match element {
        Some(ClassElement::Class(metadata)) => {
            let Some(name) = metadata.proto.companion_object_name else {
                return Ok(None);
            };
            let name = if let Some(resolver) = &metadata.names {
                resolver
                    .resolve(name)
                    .map_err(io::Error::other)?
                    .as_utf8_lossy()
                    .clone()
            } else {
                class.qualified_name.clone()
            };
            let mut buf = TextBuffer::new(cx);
            let short = get_short_name(cx, &class.qualified_name);
            buf.append_class(&short, false, &name);
            literal::add_offsets(&mut buf, cx.ir[expr].bytecode.as_ref());
            Ok(Some(buf))
        }
        Some(ClassElement::Synthetic(function)) => {
            let node = cx
                .class_nodes
                .id(&owner)
                .ok_or_else(|| invalid("Missing Kotlin synthetic lambda class"))?;
            let slot = function_slot(cx, node, &function)?;
            let mut buf = TextBuffer::new(cx);
            lambda_parameters(
                cx,
                &mut buf,
                &function,
                &function.class.qualified_name,
                indent,
                false,
            )?;
            if slot.get(cx).decompile_error().is_none()
                && let Some(root) = slot.get(cx).root()
            {
                let method = &slot.get(cx).method;
                let key = make_unique_key(&method.name, &method.descriptor);
                slot.with_current(cx, |cx| {
                    append_body(cx, &mut buf, root, &class.qualified_name, &key, indent + 1)
                })?;
            }
            if slot.get(cx).decompile_error().is_some() {
                super::dump_error(cx, node, slot.index(), &mut buf, indent + 1);
            }
            buf.append_indent(indent).append_char('}');
            literal::add_offsets(&mut buf, cx.ir[expr].bytecode.as_ref());
            Ok(Some(buf))
        }
        Some(ClassElement::FailedLambda) => Err(invalid("Kotlin synthetic lambda body is missing")),
        Some(ClassElement::FunctionReference) => {
            let node = cx
                .class_nodes
                .id(&owner)
                .ok_or_else(|| invalid("Missing Kotlin function reference class"))?;
            stringify_reference(cx, expr, node, indent, None)
        }
        _ => Ok(None),
    }
}

pub(crate) fn allocation_expression(
    cx: &mut Cx,
    expr: ExprId,
    indent: i32,
) -> io::Result<Option<TextBuffer>> {
    let ExprKind::New {
        new_type,
        constructor,
        anonymous,
        lambda,
        ..
    } = &cx.ir[expr].kind
    else {
        unreachable!("Expected a Kotlin allocation expression")
    };
    let (constructor, anonymous, lambda) = (*constructor, *anonymous, *lambda);
    let node = cx.class_nodes.id(new_type.name());
    if let Some(node) = node {
        let class = cx.class_nodes[node].class.clone();
        if members::select_language(cx, &class) {
            let element = cx
                .kotlin_members()
                .and_then(|members| members.class(&class))
                .cloned();
            if matches!(element, Some(ClassElement::FunctionReference)) {
                let receiver = constructor
                    .and_then(|call| match &cx.ir[call].kind {
                        ExprKind::Invocation(invocation) => invocation.parameters.first().copied(),
                        _ => None,
                    })
                    .ok_or_else(|| {
                        invalid("Kotlin function reference has no constructor receiver")
                    })?;
                if let Some(reference) =
                    stringify_reference(cx, expr, node, indent, Some(receiver))?
                {
                    return Ok(Some(reference));
                }
            }
            if cx.class_nodes[node].kind == ClassKind::Local
                && matches!(element, Some(ClassElement::Class(_)))
            {
                cx.class_nodes[node].kind = ClassKind::Anonymous;
                return write_anonymous_class(cx, expr, node, indent).map(Some);
            }
        }
    }

    if lambda {
        let node = node.ok_or_else(|| invalid("Missing Kotlin invokedynamic lambda class"))?;
        let info = cx.class_nodes[node]
            .lambda
            .clone()
            .ok_or_else(|| invalid("Missing Kotlin invokedynamic lambda information"))?;
        if let Some((_, local_name)) = info.content_method_name.split_once("$lambda$") {
            let lambda_name = format!("lambda_{}", local_name.replace('$', "_"));
            return invokedynamic_lambda(cx, node, indent, &info, &lambda_name).map(Some);
        }
    } else if anonymous {
        let node = node.ok_or_else(|| invalid("Missing Kotlin anonymous class"))?;
        return write_anonymous_class(cx, expr, node, indent).map(Some);
    }
    Ok(None)
}

fn write_anonymous_class(
    cx: &mut Cx,
    expr: ExprId,
    node: ClassNodeId,
    indent: i32,
) -> io::Result<TextBuffer> {
    let mut buf = TextBuffer::new(cx);
    literal::add_offsets(&mut buf, cx.ir[expr].bytecode.as_ref());
    super::write_class(cx, node, &mut buf, indent)?;
    Ok(buf)
}

fn stringify_reference(
    cx: &mut Cx,
    expr: ExprId,
    node: ClassNodeId,
    indent: i32,
    receiver: Option<ExprId>,
) -> io::Result<Option<TextBuffer>> {
    if cx
        .class_nodes
        .wrapper_owner(node)
        .is_none_or(|owner| cx.class_nodes[owner].wrapper.is_none())
    {
        return Err(invalid("Kotlin function reference class was not processed"));
    }
    let descriptor = if receiver.is_some() {
        "(Ljava/lang/Object;)V"
    } else {
        "()V"
    };
    let key = make_unique_key("<init>", descriptor);
    let Some(init) = MethodSlot::by_key(cx, node, &key) else {
        return Ok(None);
    };
    let root = init
        .get(cx)
        .root()
        .ok_or_else(|| invalid("Kotlin function reference has no constructor root"))?;
    let Some(expressions) = cx.ir[root].first.and_then(|first| cx.ir[first].exprents) else {
        return Ok(None);
    };
    let &[super_call] = cx.ir[expressions].as_slice() else {
        return Ok(None);
    };
    let ExprKind::Invocation(invoke) = &cx.ir[super_call].kind else {
        return Err(invalid(
            "Kotlin function reference constructor has no invocation",
        ));
    };
    let index = if receiver.is_some() { 2 } else { 1 };
    let [class, method, signature] = invoke
        .parameters
        .get(index..index + 3)
        .ok_or_else(|| invalid("Kotlin reference constructor has too few arguments"))?
    else {
        unreachable!()
    };
    let class = reference_constant(cx, *class)?;
    let method = reference_constant(cx, *method)?;
    let signature = reference_constant(cx, *signature)?;
    let width = method.utf16().count();
    if width > signature.utf16().count() {
        return Err(invalid("Kotlin function reference descriptor is missing"));
    }
    let descriptor = JavaString::from_utf16(signature.utf16().skip(width).collect());
    let (class, method, descriptor) = (
        class.as_utf8_lossy(),
        method.as_utf8_lossy(),
        descriptor.as_utf8_lossy(),
    );
    let target = cx.classes().get_class(class);
    let mut buf = TextBuffer::new(cx);
    literal::add_offsets(&mut buf, cx.ir[expr].bytecode.as_ref());
    if method == "<init>" {
        let ty = VarType::from_signature_cl(class, true);
        let name = kotlin_type(cx, Some(&ty), true)?;
        buf.append("::")
            .append_method(&name, false, class, method, descriptor);
        return Ok(Some(buf));
    }
    if let Some(receiver) = receiver {
        buf.append_buffer(&body::expression(cx, receiver, indent)?);
    } else if !matches!(
        target
            .as_ref()
            .and_then(|class| cx.kotlin_members()?.class(class)),
        Some(ClassElement::File(_))
    ) {
        let ty = VarType::from_signature_cl(class, true);
        let name = kotlin_type(cx, Some(&ty), true)?;
        buf.append_type_name_with(cx, &name, &ty);
    }
    buf.append("::")
        .append_method(method, false, class, method, descriptor);
    Ok(Some(buf))
}

fn reference_constant(cx: &Cx, expr: ExprId) -> io::Result<JavaString> {
    let ExprKind::Constant { value, .. } = &cx.ir[expr].kind else {
        return Err(invalid(
            "Kotlin function reference argument is not a constant",
        ));
    };
    value
        .java_string()
        .ok_or_else(|| invalid("Kotlin function reference argument is null"))
}

fn invokedynamic_lambda(
    cx: &mut Cx,
    node: ClassNodeId,
    indent: i32,
    info: &LambdaInformation,
    lambda_name: &str,
) -> io::Result<TextBuffer> {
    let slot = MethodSlot::by_key(cx, node, &info.content_method_key)
        .ok_or_else(|| invalid("Kotlin invokedynamic lambda body is missing"))?;
    let wrapper = slot.get(cx);
    let method = wrapper.method.clone();
    let processor = wrapper.variables;
    let referenced = MethodDescriptor::parse_descriptor(&info.method_descriptor);
    let actual = MethodDescriptor::parse_descriptor(&info.content_method_descriptor);
    let mut buf = TextBuffer::new(cx);
    buf.append("{ ");
    if !referenced.params.is_empty() {
        let start = actual
            .params
            .len()
            .checked_sub(referenced.params.len())
            .ok_or_else(|| {
                invalid("Kotlin invokedynamic lambda captures exceed its real signature")
            })?;
        let mut index = i32::from(!info.is_content_method_static);
        for (position, ty) in actual.params.iter().enumerate() {
            if position < start {
                index += ty.stack_size;
                continue;
            }
            if position > start {
                buf.append(", ");
            }
            let variable = VarVersionPair::new(index, 0);
            let name = cx.ir[processor]
                .clashing_names
                .get(&variable)
                .or_else(|| {
                    cx.ir[processor]
                        .names
                        .get(&variable)
                        .and_then(Option::as_ref)
                })
                .cloned()
                .unwrap_or_else(|| format!("param{index}").into());
            let options = cx.options.clone();
            let name = method
                .with_variable_namer(&options, |namer| {
                    namer.rename_parameter(cx, &method, ty, Some(name), index)
                })?
                .ok_or_else(|| invalid("Kotlin invokedynamic lambda parameter has no name"))?;
            let spelling = kotlin_type(cx, Some(ty), true)?;
            buf.append_variable(
                &name,
                true,
                true,
                &info.content_class_name,
                &info.content_method_name,
                actual.clone(),
                index,
                &name,
            )
            .append(": ")
            .append_type_name_with(cx, &spelling, ty);
            index += ty.stack_size;
        }
        buf.append(" ->");
    }
    buf.append_line_separator();

    if slot.get(cx).decompile_error().is_none()
        && let Some(root) = slot.get(cx).root()
    {
        slot.with_current(cx, |cx| {
            let render = catch_method_failure(|| {
                let exits = lambda_exits(cx, root)?;
                if exits.len() > 1 {
                    buf.prepend(&format!("{lambda_name}@"));
                    for expr in exits {
                        body::set_lambda_name(cx, expr, lambda_name.to_owned());
                    }
                }
                let owner = cx.class_nodes[node].class.qualified_name.clone();
                append_body(
                    cx,
                    &mut buf,
                    root,
                    &owner,
                    &info.content_method_key,
                    indent + 1,
                )
            });
            if let Err(error) = render {
                if error.kind() == io::ErrorKind::Interrupted {
                    return Err(error);
                }
                log::warn!(
                    "Lambda {} {} in class {} couldn't be written: {error}",
                    info.content_method_name,
                    info.content_method_descriptor,
                    cx.class_nodes[node].class.qualified_name
                );
                slot.record_write_error(cx, error);
            }
            Ok::<_, io::Error>(())
        })?;
    }
    if cx.options.dump_exception_on_error
        && let Some(error) = slot.get(cx).decompile_error()
    {
        for line in crate::engine::class_writer::exception_details(cx, error) {
            buf.append_indent(indent + 1)
                .append("// ")
                .append(&line)
                .append_line_separator();
        }
    }
    buf.append_indent(indent).append_char('}');
    Ok(buf)
}

fn lambda_exits(cx: &Cx, root: StatId) -> io::Result<Vec<ExprId>> {
    let StatementKind::Root { dummy_exit, .. } = cx.ir[root].kind else {
        unreachable!()
    };
    let mut exits = Vec::new();
    for edge in dummy_exit.get_predecessor_edges(&cx.ir, EdgeType::Break.mask()) {
        let source = cx.ir[edge].source;
        let list = cx.ir[source]
            .exprents
            .ok_or_else(|| invalid("Kotlin lambda exit has no expression list"))?;
        exits.extend(cx.ir[list].iter().copied().filter(|&expr| {
            matches!(cx.kotlin_expr(expr), Some(KotlinExpr::Exit { .. }))
                && matches!(
                    cx.ir[expr].kind,
                    ExprKind::Exit {
                        kind: ExitType::Return,
                        ..
                    }
                )
        }));
    }
    Ok(exits)
}

fn function_slot(cx: &Cx, node: ClassNodeId, function: &KFunction) -> io::Result<MethodSlot> {
    let key = make_unique_key(&function.method.name, &function.method.descriptor);
    MethodSlot::by_key(cx, node, &key)
        .ok_or_else(|| invalid("Kotlin synthetic lambda body is missing"))
}

fn append_body(
    cx: &mut Cx,
    buf: &mut TextBuffer,
    root: StatId,
    owner: &str,
    key: &str,
    indent: i32,
) -> io::Result<()> {
    let mut output = body::statement(cx, root, indent)?;
    let StatementKind::Root { dummy_exit, .. } = cx.ir[root].kind else {
        unreachable!()
    };
    let StatementKind::DummyExit { ref bytecode } = cx.ir[dummy_exit].kind else {
        unreachable!()
    };
    literal::add_offsets(&mut output, bytecode.as_ref());
    buf.append_buffer_for(&output, Some(owner), Some(key));
    Ok(())
}

fn invalid(message: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}
