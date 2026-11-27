use std::io;

use arcstr::ArcStr;

use crate::{
    code::code_constants::{ACC_ABSTRACT, ACC_FINAL, ACC_NATIVE, ACC_STATIC, ACC_VARARGS},
    decompiler::vars::{var_version_pair::VarVersionPair, versions::FinalType},
    engine::Cx,
    kotlin::{identifier, types::kotlin_type},
    structs::{StructMember, StructMethod},
    types::{GenericMethodDescriptor, MethodDescriptor},
    util::text_buffer::TextBuffer,
};

use super::{annotations, append_kotlin_type, invalid, modifiers};

pub(super) struct Header<'a> {
    pub method: &'a StructMethod,
    pub name: &'a str,
    pub descriptor: &'a MethodDescriptor,
    pub signature: Option<&'a GenericMethodDescriptor>,
    pub flags: i32,
    pub is_interface: bool,
    pub enum_constructor: bool,
}

pub(super) fn append(
    cx: &mut Cx,
    buffer: &mut TextBuffer,
    header: Header<'_>,
    indent: i32,
) -> io::Result<usize> {
    let method = header.method;
    let signature = header.signature;
    let params = &header.descriptor.params;
    let wrapper = cx
        .writing_method()
        .expect("Kotlin parameter writer entered a wrapper");
    let variables = wrapper.variables;
    let mask = wrapper.synthetic_parameters.clone();
    if mask.as_ref().is_some_and(|mask| mask.len() < params.len()) {
        return Err(invalid(
            "Kotlin synthetic parameter mask is shorter than its descriptor",
        ));
    }
    let visible = |index: usize| mask.as_ref().is_none_or(|mask| mask[index].is_none());
    let mut start = if header.enum_constructor { 2 } else { 0 };
    let mut slot = if header.enum_constructor {
        3
    } else {
        i32::from(!method.has_modifier(ACC_STATIC))
    };

    if let Some(signature) = signature.filter(|sig| !sig.type_parameters.is_empty()) {
        modifiers::append_type_parameters(
            cx,
            buffer,
            &signature.type_parameters,
            &signature.type_parameter_bounds,
        )?;
        buffer.append_char(' ');
    }

    let mut count = 0;
    let extension = variable_name(cx, variables, VarVersionPair::new(slot, 0))
        .is_some_and(|name| name.starts_with("$this$"));
    if extension {
        let receiver = signature
            .and_then(|sig| sig.parameter_types.first())
            .or_else(|| params.first())
            .ok_or_else(|| invalid("Kotlin extension has no receiver type"))?;
        let name = kotlin_type(cx, Some(receiver), true)?;
        let nullable = annotations::parameter(cx, buffer, &method.attributes, 0)?;
        append_kotlin_type(buffer, receiver, &name, true, nullable);
        buffer.append_char('.');
        count += 1;
        start += 1;
        slot += receiver.stack_size;
    }

    buffer.append(&identifier(header.name)).append_char('(');
    let last_visible = (0..params.len()).rev().find(|&index| visible(index));
    if last_visible.is_some() {
        buffer
            .push_newline_group(indent, 1)
            .append_possible_newline();
    }
    let metadata = method
        .attributes
        .method_parameters
        .as_ref()
        .filter(|_| cx.options.use_method_parameters);
    let mut first = true;
    buffer.push_newline_group(indent, 0);
    for (index, erased) in params.iter().enumerate().skip(start) {
        let mut ty = signature
            .and_then(|sig| sig.parameter_types.get(count))
            .unwrap_or(erased);
        let element;
        if visible(index) {
            if !first {
                buffer
                    .append_char(',')
                    .append_possible_newline_or(" ", false);
            }
            first = false;
            let nullable = annotations::parameter(cx, buffer, &method.attributes, count)?;
            let is_vararg =
                last_visible == Some(index) && method.has_modifier(ACC_VARARGS) && ty.array_dim > 0;
            if is_vararg {
                buffer.append("vararg ");
            }
            let param_meta = metadata.and_then(|meta| meta.entries.get(index));
            let var = VarVersionPair::new(slot, 0);
            let name = if let Some(meta) = param_meta {
                meta.name.as_ref()
            } else {
                variable_name(cx, variables, var)
            };
            let name = if header.flags & (ACC_ABSTRACT | ACC_NATIVE) != 0 {
                // The bundled providers inherit renameAbstractParameter's identity method.
                // KotlinWriter invokes it directly, bypassing renameParameter.
                let name = name.ok_or_else(|| invalid("Missing Kotlin abstract parameter name"))?;
                Some(cx.struct_context.rename_abstract_parameter(
                    &method.class_qualified_name,
                    &method.name,
                    &method.descriptor,
                    slot - i32::from(header.flags & ACC_STATIC == 0),
                    name,
                ))
            } else {
                name.map(ArcStr::as_str)
            };
            if let Some(name) = name {
                buffer.append(&identifier(name));
            } else {
                buffer.append(&format!("param{slot}"));
            }
            buffer.append(": ");
            if let Some(meta) = param_meta {
                modifiers::append_modifiers(
                    buffer,
                    meta.access_flags,
                    ACC_FINAL,
                    header.is_interface,
                    0,
                );
            } else if cx.ir[variables].versions.final_vars.get(&var)
                == Some(&FinalType::ExplicitFinal)
            {
                buffer.append("final ");
            }
            if is_vararg {
                element = ty.decrease_array_dim();
                ty = &element;
            }
            let name = kotlin_type(cx, Some(ty), true)?;
            append_kotlin_type(buffer, ty, &name, nullable, nullable);
            count += 1;
        }
        slot += ty.stack_size;
    }
    buffer.pop_newline_group();
    if last_visible.is_some() {
        buffer
            .append_possible_newline_or("", true)
            .pop_newline_group();
    }
    buffer.append_char(')');
    Ok(count)
}

fn variable_name(
    cx: &Cx,
    variables: crate::decompiler::ir::VarProcessorId,
    pair: VarVersionPair,
) -> Option<&ArcStr> {
    cx.ir[variables].names.get(&pair).and_then(Option::as_ref)
}
