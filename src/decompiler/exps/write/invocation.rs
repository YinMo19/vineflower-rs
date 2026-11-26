// Copyright 2000-2018 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! InvocationExprent source writing and argument-list reuse by NewExprent.

mod classpath;
mod overloads;

use std::io;
use std::sync::Arc;

use super::casts::{CastOptions, NullCastType, append_casted};
use super::fields::{allows_newline_after_qualifier, mark_qualifier, write_qualified_super};
use super::variables::NAMELESS_ENCLOSURE;
use crate::code::code_constants::{
    ACC_ENUM, ACC_INTERFACE, ACC_VARARGS, CONSTANT_CLASS, CONSTANT_STRING, is_return_polymorphic,
};
use crate::decompiler::exps::{
    Expr, ExprKind, FunctionType, Invocation, InvocationFunction, InvocationType, WriteFlags,
    expr_util::synthetic_parameters_mask, generic_inference::Inference, literal,
};
use crate::decompiler::ir::ExprId;
use crate::engine::Cx;
use crate::engine::class_nodes::ClassKind;
use crate::engine::import_collector::{get_short_name_in_class_context, java_class_name};
use crate::structs::consts::PooledConstant;
use crate::structs::{StructClass, StructMember};
use crate::types::{CodeType, GenericsMap, MethodDescriptor, TypeFamily, VarType};
use crate::util::jhash::JHashSet;
use crate::util::text_buffer::TextBuffer;
use crate::util::text_util::to_valid_java_identifier;

use self::overloads::{
    ambiguous_parameters, can_access, is_varargs_ambiguous, matched_descriptors, ranks_match,
};

const CAST_PRECEDENCE: i32 = 2;

pub(super) fn invocation(cx: &mut Cx, expr: ExprId, indent: i32) -> io::Result<TextBuffer> {
    let invoke = call(cx, expr);
    let class = invoke
        .classname
        .clone()
        .ok_or_else(|| invalid("Invocation has no owner"))?;
    let kind = invoke.kind;
    let function = invoke.function;
    let receiver = invoke.instance;
    let static_qualifier = invoke.is_static
        || matches!(
            kind,
            InvocationType::Dynamic | InvocationType::ConstantDynamic
        );
    let mut buffer = TextBuffer::new(cx);
    if invoke.was_lazy_condy {
        buffer.append("/* $VF: constant dynamic replaced with non-lazy method call */ ");
    }

    if let Some(receiver) = receiver
        && let ExprKind::Invocation(receiver) = &mut cx.ir[receiver].kind
    {
        receiver.can_ignore_boxing = false;
    }

    let mut super_qualifier = None;
    let mut instance_is_this = false;
    let mut call_chain_group = false;
    if static_qualifier {
        let invoke = call(cx, expr);
        if invoke.can_ignore_boxing && !invoke.force_boxing && invoke.is_boxing_call(cx) {
            let param = invoke.parameters[0];
            let primitive = invoke.descriptor.params[0].clone();
            append_casted(
                cx,
                param,
                &primitive,
                &mut buffer,
                indent,
                CastOptions {
                    cast_narrowing: true,
                    ..CastOptions::default()
                },
            )?;
            add_mapping(cx, expr, &mut buffer);
            return Ok(buffer);
        }
        if kind == InvocationType::ConstantDynamic {
            let return_type = invoke.descriptor.ret.clone();
            buffer
                .append_char('(')
                .append_cast_type_name(cx, &return_type)
                .append_char(')');
        }
        if cx.current_class_node.as_deref() != Some(class.as_str()) {
            let qualified = java_class_name(cx, &class);
            let qualifier = get_short_name_in_class_context(cx, &qualified);
            buffer.append_all_classes(&qualifier, &class);
        }
    } else {
        if let Some(receiver) = receiver
            && let Some(this_class) = this_class(cx, receiver)
        {
            instance_is_this = true;
            if kind == InvocationType::Special && class != *this_class {
                super_qualifier = Some(
                    if cx
                        .classes()
                        .get_class(&class)
                        .is_some_and(|class| class.has_modifier(ACC_INTERFACE))
                    {
                        class.clone()
                    } else {
                        this_class.clone()
                    },
                );
            }
        }
        let invoke = call(cx, expr);
        if is_return_polymorphic(&class, &invoke.name)
            && invoke.descriptor.ret != VarType::VARTYPE_VOID
        {
            let return_type = invoke.descriptor.ret.clone();
            buffer
                .append_char('(')
                .append_cast_type_name(cx, &return_type)
                .append_char(')');
        }
        if function == InvocationFunction::General {
            if let Some(qualifier) = &super_qualifier {
                write_qualified_super(cx, &mut buffer, qualifier)?;
            } else if let Some(receiver) = receiver {
                let left = receiver_type(cx, expr, &class);
                let right = {
                    let mut inference = Inference::for_writing(cx);
                    inference.mark_instance(receiver);
                    inference.infer(receiver, Some(&left))?
                };
                if call(cx, expr).is_unboxing_call()
                    && !cx.ir[expr].write_flags.contains(WriteFlags::FORCE_UNBOXING)
                {
                    return write_implicit_unboxing(
                        cx, expr, receiver, &class, &left, buffer, indent,
                    );
                }
                mark_qualifier(cx, receiver);
                if !cx.ir[expr].write_flags.contains(WriteFlags::QUALIFIER) {
                    buffer.push_newline_group(indent, 1);
                    call_chain_group = true;
                }
                let mut instance = super::to_java(cx, receiver, indent)?;
                let instance_precedence = super::precedence(cx, receiver)?;
                let cast = if right == VarType::VARTYPE_OBJECT
                    && left != right
                    && cx
                        .class_nodes
                        .get(&class)
                        .is_some_and(|node| node.kind != ClassKind::Anonymous)
                {
                    Some(left)
                } else {
                    call(cx, expr)
                        .generics
                        .as_ref()
                        .and_then(|state| state.remapped_instance.clone())
                };
                if let Some(cast) = cast {
                    if instance_precedence >= CAST_PRECEDENCE {
                        instance.enclose_with_parens();
                    }
                    buffer
                        .append("((")
                        .append_cast_type_name(cx, &cast)
                        .append_char(')')
                        .append_buffer(&instance)
                        .append_char(')');
                } else if instance_precedence > super::precedence(cx, expr)?
                    && !can_skip_parens(cx, receiver)
                {
                    buffer
                        .append_char('(')
                        .append_buffer(&instance)
                        .append_char(')');
                } else {
                    let nio_buffer = VarType::with_value(
                        CodeType::Object,
                        0,
                        arcstr::literal!("java/nio/Buffer"),
                    );
                    if call(cx, expr).descriptor.ret == nio_buffer
                        && right != nio_buffer
                        && right
                            .value
                            .as_deref()
                            .is_some_and(|name| cx.classes().instance_of(name, "java/nio/Buffer"))
                    {
                        buffer
                            .append("((")
                            .append_cast_type_name(cx, &nio_buffer)
                            .append_char(')')
                            .append_buffer(&instance)
                            .append_char(')');
                    } else {
                        buffer.append_buffer(&instance);
                    }
                }
                if allows_newline_after_qualifier(cx, receiver) {
                    buffer.append_possible_newline();
                }
            }
        }
    }
    match function {
        InvocationFunction::General => {
            if buffer.content_equals(NAMELESS_ENCLOSURE) {
                buffer.set_length(0);
            }
            if buffer.length() > 0 {
                buffer.append_char('.');
                append_invocation_type_arguments(cx, expr, &mut buffer);
            }
            add_mapping(cx, expr, &mut buffer);
            append_method_selector(cx, expr, &mut buffer, &class)?;
            buffer.append_char('(');
        }
        InvocationFunction::Clinit => return Err(invalid("Explicit invocation of <clinit>")),
        InvocationFunction::Init => {
            add_mapping(cx, expr, &mut buffer);
            if super_qualifier.is_some() {
                buffer.append("super(");
            } else if instance_is_this {
                buffer.append("this(");
            } else if let Some(receiver) = receiver {
                buffer
                    .append_buffer(&super::to_java(cx, receiver, indent)?)
                    .append_char('.');
                if cx.options.decompiler_comments {
                    buffer.append("/* $VF: Unable to resugar constructor */");
                }
                buffer.append("<init>(");
            } else {
                return Err(invalid("Unrecognized invocation of <init>"));
            }
        }
    }
    buffer
        .append_buffer(&append_param_list(cx, expr, indent)?)
        .append_char(')');
    if call_chain_group {
        buffer.pop_newline_group();
    }
    Ok(buffer)
}

fn this_class(cx: &Cx, expr: ExprId) -> Option<&arcstr::ArcStr> {
    let ExprKind::Variable(variable) = &cx.ir[expr].kind else {
        return None;
    };
    let processor = variable
        .processor
        .or_else(|| cx.writing_method().map(|method| method.variables))?;
    cx.ir[processor].this_vars.get(&variable.pair())
}

fn receiver_type(cx: &Cx, expr: ExprId, class: &arcstr::ArcStr) -> VarType {
    if let Some(generics) = &call(cx, expr).generics
        && !generics.mappings.is_empty()
        && let Some(signature) = cx
            .classes()
            .get_class(class)
            .and_then(|class| class.signature())
        && let Some(remapped) = signature
            .generic_type
            .remap_for_inference(&generics.mappings)
        && !remapped.same_generic_reference(&signature.generic_type)
    {
        return remapped;
    }
    VarType::with_value(CodeType::Object, 0, class.clone())
}

fn write_implicit_unboxing(
    cx: &mut Cx,
    expr: ExprId,
    receiver: ExprId,
    class: &str,
    left: &VarType,
    mut buffer: TextBuffer,
    indent: i32,
) -> io::Result<TextBuffer> {
    add_mapping(cx, expr, &mut buffer);
    let receiver = if let ExprKind::Function {
        op: FunctionType::Cast,
        operands,
        ..
    } = &cx.ir[receiver].kind
        && let [first, cast, ..] = operands.as_slice()
        && let ExprKind::Constant { var_type, .. } = &cx.ir[*cast].kind
        && !call(cx, expr)
            .generics
            .as_ref()
            .is_some_and(|state| state.keep_unboxing_cast)
    {
        let first = *first;
        let skip = if matches!(
            cx.ir[first].kind,
            ExprKind::Variable(_) | ExprKind::Field(_)
        ) {
            let ty = Inference::for_writing(cx).infer(first, Some(left))?;
            !matches!(ty.ty, CodeType::Object | CodeType::Genvar)
                || ty
                    .value
                    .as_deref()
                    .is_some_and(|name| cx.classes().instance_of(name, class))
        } else {
            var_type.value.as_deref() == Some(class)
        };
        if skip { first } else { receiver }
    } else {
        receiver
    };
    buffer.append_buffer(&super::to_java(cx, receiver, indent)?);
    Ok(buffer)
}

fn can_skip_parens(cx: &Cx, receiver: ExprId) -> bool {
    matches!(
        cx.ir[receiver].kind,
        ExprKind::New {
            anonymous: false,
            lambda: false,
            method_reference: false,
            ..
        }
    )
}

fn append_method_selector(
    cx: &mut Cx,
    expr: ExprId,
    buffer: &mut TextBuffer,
    class: &str,
) -> io::Result<()> {
    let invoke = call(cx, expr);
    let kind = invoke.kind;
    let dynamic = matches!(
        kind,
        InvocationType::Dynamic | InvocationType::ConstantDynamic
    );
    let bootstrap = invoke.bootstrap_method.as_ref();
    if dynamic {
        if let Some(bootstrap) = bootstrap {
            buffer.append(&bootstrap.elementname).append("<\"");
        } else {
            buffer.append_char('<');
        }
    }
    let valid = to_valid_java_identifier(&invoke.name);
    buffer.append_method_with(
        &valid,
        false,
        class,
        &invoke.name,
        invoke.descriptor.as_ref().clone(),
    );
    if valid.as_ref() != invoke.name.as_str() {
        buffer
            .append("/* $VF was: ")
            .append(&invoke.name)
            .append(" */");
    }
    if dynamic {
        if bootstrap.is_some() {
            let arguments = invoke
                .bootstrap_arguments
                .clone()
                .ok_or_else(|| invalid("Dynamic invocation has no bootstrap argument table"))?;
            buffer.append_char('"');
            for argument in arguments.iter() {
                buffer.append_char(',');
                if let Some(argument) = argument {
                    append_bootstrap_argument(cx, buffer, argument);
                }
            }
            buffer.append_char('>');
        } else if kind == InvocationType::Dynamic {
            buffer.append(">invokedynamic");
        } else {
            buffer.append(">ldc");
        }
    }
    Ok(())
}

fn append_bootstrap_argument(cx: &mut Cx, buffer: &mut TextBuffer, argument: &PooledConstant) {
    match argument {
        PooledConstant::Primitive(primitive) if primitive.ty == CONSTANT_CLASS => {
            let ty = VarType::from_signature(primitive.get_string());
            buffer.append_cast_type_name(cx, &ty);
        }
        PooledConstant::Primitive(primitive) if primitive.ty == CONSTANT_STRING => {
            let escaped = literal::escape_string(primitive.get_java_string(), false);
            buffer.append_char('"').append(&escaped).append_char('"');
        }
        PooledConstant::Primitive(primitive) => {
            let text = primitive.value.java_string();
            buffer.append(text.as_ref().map_or("null", |value| value.as_utf8_lossy()));
        }
        PooledConstant::Link(link) => {
            if let Some(class) = &link.classname {
                buffer
                    .append_cast_type_name(cx, &VarType::from_signature(class))
                    .append("::")
                    .append(&link.elementname);
            } else {
                buffer
                    .append("/* VF: Constant Dynamic */ (")
                    .append_cast_type_name(cx, &VarType::from_signature(&link.descriptor))
                    .append(") ")
                    .append(&link.elementname);
            }
        }
    }
}

/// Write the explicit type arguments of a method or allocation.
pub(super) fn append_type_arguments(cx: &mut Cx, buffer: &mut TextBuffer, arguments: &[VarType]) {
    if arguments.is_empty() {
        return;
    }
    buffer.append_char('<');
    for (index, ty) in arguments.iter().enumerate() {
        if index != 0 {
            buffer.append(", ");
        }
        buffer.append_cast_type_name(cx, ty);
    }
    buffer.append_char('>');
}

pub(super) fn append_invocation_type_arguments(cx: &mut Cx, expr: ExprId, buffer: &mut TextBuffer) {
    if let Some(generics) = &call(cx, expr).generics
        && !generics.arguments.is_empty()
    {
        let arguments = generics.arguments.clone();
        append_type_arguments(cx, buffer, &arguments);
    }
}

/// Render the part between the call's parentheses, including its formatting groups.
pub(super) fn append_param_list(cx: &mut Cx, expr: ExprId, indent: i32) -> io::Result<TextBuffer> {
    let invoke = call(cx, expr);
    let class = invoke
        .classname
        .clone()
        .ok_or_else(|| invalid("Invocation has no owner"))?;
    let node = cx.class_nodes.get(&class);
    let (mask, start) = if invoke.function == InvocationFunction::Init {
        let enum_constructor = cx.options.decompile_enums
            && node.is_some_and(|node| node.class.has_modifier(ACC_ENUM));
        (
            synthetic_parameters_mask(cx, invoke)?,
            if enum_constructor { 2 } else { 0 },
        )
    } else {
        (None, 0)
    };

    let owner = cx.classes().get_class(&class);
    let mut used_varargs = false;
    let mut matches = Vec::new();
    let mut ambiguous_varargs = false;
    let mut ambiguous_parameters_by_index = Vec::new();
    if let Some(owner) = &owner {
        let current = owner.get_method(&invoke.name, invoke.string_descriptor());
        used_varargs = current
            .cloned()
            .or_else(|| owner.get_method_recursive(cx, &invoke.name, invoke.string_descriptor()))
            .is_some_and(|method| method.has_modifier(ACC_VARARGS));
        matches = matched_descriptors(cx, invoke, owner, |_, desc| {
            ranks_match(cx, invoke, &desc.params, false, false)
        });
        if used_varargs {
            let current_varargs = current.is_some_and(|method| method.has_modifier(ACC_VARARGS));
            let possible_varargs = matched_descriptors(cx, invoke, owner, |method, desc| {
                ranks_match(
                    cx,
                    invoke,
                    &desc.params,
                    method.has_modifier(ACC_VARARGS),
                    current_varargs,
                )
            });
            ambiguous_varargs = is_varargs_ambiguous(&possible_varargs);
        }
        ambiguous_parameters_by_index = ambiguous_parameters(cx, invoke, &matches, current);
    } else if invoke.parameters.len() == invoke.descriptor.params.len()
        && let Some(&last) = invoke.parameters.last()
        && matches!(cx.ir[last].kind, ExprKind::New { .. })
    {
        used_varargs = classpath::is_varargs(cx, &class, &invoke.name, &invoke.descriptor);
    }

    let arity = invoke.parameters.len();
    let descriptor = Arc::clone(&invoke.descriptor);
    if used_varargs
        && arity == descriptor.params.len()
        && let Some(&last) = invoke.parameters.last()
        && let ExprKind::New { array_elements, .. } = &cx.ir[last].kind
        && Expr::expr_type(cx, last).array_dim >= 1
        && (!ambiguous_varargs || array_elements.len() != 1)
    {
        cx.ir[last].write_flags.insert(WriteFlags::VARARG);
    }

    if arity > descriptor.params.len() {
        return Err(invalid("Invocation has more arguments than its descriptor"));
    }
    let mut types = descriptor.params.clone();
    for index in start..arity {
        let argument = call(cx, expr).parameters[index];
        if let ExprKind::Invocation(invoke) = &cx.ir[argument].kind {
            if invoke.is_boxing_call(cx) {
                adjust_for_boxing(
                    cx,
                    expr,
                    argument,
                    index,
                    owner.as_ref(),
                    matches.len(),
                    &mut types,
                );
            } else if invoke.is_unboxing_call()
                && !cx.ir[argument]
                    .write_flags
                    .contains(WriteFlags::FORCE_UNBOXING)
                && let Some(owner) = &owner
                && let Some(receiver) = invoke.instance
                && force_unboxing_for_overload(cx, call(cx, expr), owner, index, receiver)
            {
                cx.ir[argument]
                    .write_flags
                    .insert(WriteFlags::FORCE_UNBOXING);
            }
        }
    }

    if resolved_signature_missing(cx, expr) {
        infer_for_argument_types(cx, expr)?;
    }
    let visible = |i: usize| {
        mask.as_ref()
            .is_none_or(|mask| mask.get(i).is_none_or(Option::is_none))
    };
    update_argument_types(cx, expr, &mut types, start, visible)?;

    let mut buffer = TextBuffer::new(cx);
    if arity != 0 {
        buffer
            .push_newline_group(indent, 1)
            .append_possible_newline()
            .push_newline_group(indent, 0);
    }
    let mut first = true;
    for (i, ty) in types
        .iter()
        .enumerate()
        .take(arity)
        .skip(start)
        .filter(|(i, _)| visible(*i))
    {
        let argument = call(cx, expr).parameters[i];
        if i + 1 == arity
            && Expr::expr_type(cx, argument) == VarType::VARTYPE_NULL
            && descriptor.params[i]
                .value
                .as_deref()
                .and_then(|class| cx.class_nodes.get(class))
                .is_some_and(|node| node.kind == ClassKind::Anonymous)
        {
            break;
        }
        let ambiguous = ambiguous_parameters_by_index
            .get(i)
            .copied()
            .unwrap_or(false);
        let mut output = TextBuffer::new(cx);
        append_casted(
            cx,
            argument,
            ty,
            &mut output,
            indent,
            CastOptions {
                null_cast: if ambiguous {
                    NullCastType::Cast
                } else {
                    NullCastType::DontCastAtAll
                },
                cast_always: ambiguous,
                cast_narrowing: true,
                unbox: true,
            },
        )?;
        if output.length() > 0 {
            if !first {
                buffer
                    .append_char(',')
                    .append_possible_newline_or(" ", false);
            }
            buffer.append_buffer(&output);
        }
        first = false;
    }
    if arity != 0 {
        buffer
            .pop_newline_group()
            .append_possible_newline_or("", true)
            .pop_newline_group();
    }
    Ok(buffer)
}

fn resolved_signature_missing(cx: &Cx, expr: ExprId) -> bool {
    call(cx, expr)
        .generics
        .as_ref()
        .is_none_or(|generics| generics.resolved_method.is_none())
}

fn infer_for_argument_types(cx: &mut Cx, expr: ExprId) -> io::Result<()> {
    Inference::for_writing(cx).infer(expr, None)?;
    let invoke = call(cx, expr);
    if invoke
        .generics
        .as_ref()
        .is_some_and(|state| !state.mappings.is_empty())
        || invoke.function == InvocationFunction::Init
        || invoke.instance.is_none()
    {
        return Ok(());
    }
    let instance = invoke.instance.unwrap();
    let inferred = Inference::for_writing(cx).infer(instance, None)?;
    if inferred.is_generic()
        && inferred.ty != CodeType::Genvar
        && let Some(signature) = inferred
            .value
            .as_deref()
            .and_then(|class| cx.classes().get_class(class))
            .and_then(|class| class.signature())
    {
        let mut mapping = GenericsMap::new();
        signature
            .generic_type
            .map_gen_vars_to(cx, &inferred, &mut mapping);
        Inference::for_writing(cx).invocation_state(expr).mappings = mapping;
    }
    Ok(())
}

fn update_argument_types(
    cx: &mut Cx,
    expr: ExprId,
    types: &mut [VarType],
    start: usize,
    visible: impl Fn(usize) -> bool,
) -> io::Result<()> {
    let state = match &call(cx, expr).generics {
        Some(state) => state,
        None => return Ok(()),
    };
    let Some(method) = &state.resolved_method else {
        return Ok(());
    };
    let Some(signature) = method.signature() else {
        return Ok(());
    };
    let inherited = call(cx, expr)
        .classname
        .as_deref()
        .filter(|&name| name != method.class_qualified_name.as_str())
        .and_then(|name| cx.classes().get_class(name))
        .and_then(|class| {
            class
                .get_all_generics(cx)
                .get(&method.class_qualified_name)
                .cloned()
        });
    let mut names = JHashSet::new();
    names.extend(Inference::for_writing(cx).named_generics().keys().cloned());
    let state = call(cx, expr).generics.as_ref().unwrap();
    let empty = GenericsMap::new();
    let inherited = inherited.as_deref().unwrap_or(&empty);
    let visible_types = types
        .iter_mut()
        .enumerate()
        .skip(start)
        .filter(|(i, _)| visible(*i));
    for ((_, erased), generic) in visible_types.zip(&signature.parameter_types) {
        if let Some(inherited) = generic.remap_for_inference(inherited)
            && let Some(ty) = inherited.remap_for_inference(&state.mappings)
            && (!ty.is_generic() || !ty.has_unknown_generic_type(&names))
        {
            *erased = ty;
        }
    }
    Ok(())
}

fn adjust_for_boxing(
    cx: &mut Cx,
    expr: ExprId,
    argument: ExprId,
    index: usize,
    owner: Option<&Arc<StructClass>>,
    original_matches: usize,
    types: &mut [VarType],
) {
    let boxed = call(cx, argument);
    let value = boxed.parameters[0];
    let mut ty = Expr::expr_type(cx, value);
    if ty.type_family == TypeFamily::Integer {
        ty = match boxed.classname.as_deref() {
            Some("java/lang/Short") => VarType::VARTYPE_SHORT,
            Some("java/lang/Byte") => VarType::VARTYPE_BYTE,
            Some("java/lang/Integer") => VarType::VARTYPE_INT,
            _ => VarType::VARTYPE_CHAR,
        };
    }
    types[index] = ty;
    let invoke = call(cx, expr);
    let declared = &invoke.descriptor.params;
    let now_matches = owner.map_or(0, |owner| {
        matched_descriptors(cx, invoke, owner, |_, descriptor| {
            descriptor.params.len() == declared.len()
                && descriptor.params.iter().zip(declared).zip(&*types).all(
                    |((value, declared), actual)| {
                        (value.type_family == declared.type_family
                            || value.type_family == actual.type_family)
                            && (value.array_dim == declared.array_dim
                                || value.array_dim == actual.array_dim)
                    },
                )
        })
        .len()
    });
    if now_matches != original_matches {
        types[index] = declared[index].clone();
        let ExprKind::Invocation(boxed) = &mut cx.ir[argument].kind else {
            unreachable!()
        };
        boxed.force_boxing = true;
    } else {
        // The cast writer still receives the original boxed expression.
        let bytecode = cx.ir[argument].bytecode.clone();
        Expr::add_offsets(&mut cx.ir, value, bytecode.as_ref());
    }
}

fn force_unboxing_for_overload(
    cx: &Cx,
    invoke: &Invocation,
    owner: &StructClass,
    index: usize,
    receiver: ExprId,
) -> bool {
    let receiver_type = Expr::expr_type(cx, receiver);
    let Some(receiver_type) = receiver_type.value.as_deref() else {
        return false;
    };
    owner
        .methods
        .iter()
        .filter(|method| {
            method.name == invoke.name
                && can_access(cx, method)
                && method.descriptor.as_str() != invoke.string_descriptor()
        })
        .any(|method| {
            let other = MethodDescriptor::parse_descriptor(&method.descriptor);
            other.params.len() == invoke.descriptor.params.len()
                && other.params[index].ty == CodeType::Object
                && cx
                    .classes()
                    .instance_of(receiver_type, other.params[index].name())
        })
}

fn add_mapping(cx: &Cx, expr: ExprId, buffer: &mut TextBuffer) {
    literal::add_offsets(buffer, cx.ir[expr].bytecode.as_ref());
}

fn call(cx: &Cx, expr: ExprId) -> &Invocation {
    let ExprKind::Invocation(call) = &cx.ir[expr].kind else {
        unreachable!("Invocation writer received a different expression");
    };
    call
}

fn invalid(message: impl Into<String>) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message.into())
}
