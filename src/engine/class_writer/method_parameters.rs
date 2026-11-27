//! ClassWriter.writeMethodParameterHeader.

use std::io;

use arcstr::ArcStr;

use super::annotations::append_parameter_annotations;
use super::type_annotations::TypeAnnotations;
use crate::code::code_constants::{ACC_ABSTRACT, ACC_FINAL, ACC_NATIVE, ACC_STATIC, ACC_VARARGS};
use crate::decompiler::expr_processor::get_cast_type_name;
use crate::decompiler::exps::expr_util::visible_parameters;
use crate::decompiler::vars::{var_version_pair::VarVersionPair, versions::FinalType};
use crate::engine::{Cx, class_wrapper::MethodSlot};
use crate::structs::{StructClass, StructMember, StructMethod, attr::TypeAnnotationData};
use crate::types::{GenericMethodDescriptor, MethodDescriptor, VarType};
use crate::util::text_buffer::TextBuffer;

pub(super) struct ParameterHeader<'a> {
    pub method: &'a StructMethod,
    pub class: &'a StructClass,
    pub descriptor: &'a MethodDescriptor,
    pub generic: Option<&'a GenericMethodDescriptor>,
    pub slot: MethodSlot,
    pub flags: i32,
    pub enum_constructor: bool,
}

pub(super) fn append(
    cx: &mut Cx,
    buffer: &mut TextBuffer,
    header: ParameterHeader<'_>,
    indent: i32,
) -> io::Result<usize> {
    let method = header.method;
    let params = &header.descriptor.params;
    let mask = header.slot.get(cx).synthetic_parameters.clone();
    let visible = visible_parameters(mask.as_deref());
    let last_visible = (0..params.len()).rev().find(|&index| visible(index));
    buffer.append_char('(');
    if last_visible.is_some() {
        buffer
            .push_newline_group(indent, 1)
            .append_possible_newline();
    }
    buffer.push_newline_group(indent, 0);

    let metadata = if cx.options.use_method_parameters {
        method.attributes.method_parameters.as_ref()
    } else {
        None
    };
    let variables = header.slot.get(cx).variables;
    let start = if header.enum_constructor { 2 } else { 0 };
    let mut slot = if header.enum_constructor {
        3
    } else {
        i32::from(!method.has_modifier(ACC_STATIC))
    };
    let mut count = 0;
    for (index, erased) in params.iter().enumerate().skip(start) {
        if !visible(index) {
            slot += erased.stack_size;
            continue;
        }
        let mut ty = header
            .generic
            .and_then(|sig| sig.parameter_types.get(count))
            .unwrap_or(erased)
            .clone();
        if count != 0 {
            buffer
                .append_char(',')
                .append_possible_newline_or(" ", false);
        }
        let filter = append_parameter_annotations(cx, buffer, &method.attributes, count)?;
        let pair = VarVersionPair::new(slot, 0);
        let metadata = metadata.and_then(|attribute| attribute.entries.get(index));
        let explicit_final = metadata.map_or_else(
            || cx.ir[variables].versions.final_vars.get(&pair) == Some(&FinalType::ExplicitFinal),
            |entry| entry.access_flags & ACC_FINAL != 0,
        );
        if explicit_final {
            buffer.append("final ");
        }

        let vararg =
            last_visible == Some(index) && method.has_modifier(ACC_VARARGS) && ty.array_dim > 0;
        if vararg {
            ty = ty.decrease_array_dim();
        }
        let mut text = get_cast_type_name(cx, &ty);
        if text == "<undefinedtype>" && cx.options.undefined_as_object {
            text = get_cast_type_name(cx, &VarType::VARTYPE_OBJECT);
        }
        let mut paths = TypeAnnotations::for_target(
            &method.attributes,
            TypeAnnotationData::METHOD_PARAMETER,
            count as i32,
        );
        if paths.is_empty() {
            buffer.append_cast_type_name_with(cx, &text, &ty);
            if vararg {
                buffer.append("...");
            }
        } else {
            let annotated = if vararg {
                ty.resize_array_dim(ty.array_dim + 1)
            } else {
                ty.clone()
            };
            buffer.append_annotated_cast_type_name(
                cx, &annotated, &mut paths, &filter, vararg, true,
            )?;
        }
        buffer.append_char(' ');

        let processor = &cx.ir[variables];
        let name = processor
            .clashing_names
            .get(&pair)
            .or_else(|| metadata.and_then(|entry| entry.name.as_ref()))
            .or_else(|| processor.names.get(&pair).and_then(Option::as_ref))
            .cloned();
        let name = rename(cx, &header, &ty, name, slot)?;
        let fallback;
        let (text, token_name) = if let Some(name) = &name {
            (name.as_str(), name.as_str())
        } else {
            fallback = format!("param{slot}");
            (fallback.as_str(), "null")
        };
        buffer.append_variable(
            text,
            true,
            true,
            &header.class.qualified_name,
            &method.name,
            header.descriptor.clone(),
            slot,
            token_name,
        );
        count += 1;
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

fn rename(
    cx: &mut Cx,
    header: &ParameterHeader<'_>,
    ty: &VarType,
    name: Option<ArcStr>,
    slot: i32,
) -> io::Result<Option<ArcStr>> {
    let method = header.method;
    let renamed = rename_parameter(cx, method, ty, name.clone(), slot)?;
    if renamed == name
        && header.flags & (ACC_ABSTRACT | ACC_NATIVE) != 0
        && let Some(mapped) = cx.struct_context.abstract_parameter_name(
            &method.class_qualified_name,
            &method.name,
            &method.descriptor,
            slot - i32::from(header.flags & ACC_STATIC == 0),
        )
    {
        return Ok(Some(mapped.into()));
    }
    Ok(renamed)
}

pub(super) fn rename_parameter(
    cx: &mut Cx,
    method: &StructMethod,
    ty: &VarType,
    name: Option<ArcStr>,
    slot: i32,
) -> io::Result<Option<ArcStr>> {
    let options = cx.options.clone();
    method.with_variable_namer(&options, |namer| namer.rename_parameter(cx, method, ty, name, slot))
}
