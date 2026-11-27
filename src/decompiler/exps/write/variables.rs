//! Local declarations, captured receivers, and variable source tokens.

use std::io;

use arcstr::ArcStr;

use crate::code::code_constants::ACC_STATIC;
use crate::decompiler::expr_processor::get_cast_type_name;
use crate::decompiler::exps::{Expr, Variable, WriteFlags, literal};
use crate::decompiler::ir::ExprId;
use crate::decompiler::vars::versions::FinalType;
use crate::engine::{Cx, class_wrapper::MethodWrapper};
use crate::structs::StructMember;
use crate::types::{MethodDescriptor, VarType, generic_main};
use crate::util::{text_buffer::TextBuffer, text_util::is_java_identifier};

pub(super) const NAMELESS_ENCLOSURE: &str = "<VAR_NAMELESS_ENCLOSURE>";

pub(super) fn to_java(cx: &mut Cx, expr: ExprId, indent: i32) -> io::Result<TextBuffer> {
    let variable = Expr::variable(&cx.ir, expr)
        .expect("Expected a variable")
        .clone();
    let mut buffer = TextBuffer::new(cx);
    literal::add_offsets(&mut buffer, cx.ir[expr].bytecode.as_ref());

    if variable.class_definition {
        let class = variable
            .var_type
            .as_ref()
            .and_then(|ty| ty.value.as_deref())
            .and_then(|name| cx.class_nodes.id(name))
            .ok_or_else(|| invalid("Missing local class definition"))?;
        crate::engine::class_writer::write_class(cx, class, &mut buffer, indent)?;
        return Ok(buffer);
    }

    let pair = variable.pair();
    if variable.definition {
        if !cx.ir[expr]
            .write_flags
            .contains(WriteFlags::WRITING_PATTERN)
            && variable.processor.is_some_and(|owner| {
                cx.ir[owner].versions.final_vars.get(&pair) == Some(&FinalType::ExplicitFinal)
            })
        {
            buffer.append("final ");
        }
        let ty = definition_type(cx, expr, &variable);
        let name = get_cast_type_name(cx, &ty);
        if name == "<unrepresentable>" || variable.intersection_type {
            buffer.append("var");
        } else {
            buffer.append_cast_type_name(cx, &ty);
        }
        buffer.append_char(' ');
    }

    let fallback = if pair.version == 0 {
        format!("var{}", pair.var)
    } else {
        format!("var{}_{}", pair.var, pair.version)
    };
    let processor = variable.processor.map(|owner| &cx.ir[owner]);
    let name = processor
        .and_then(|proc| proc.clashing_names.get(&pair))
        .or_else(|| {
            variable
                .lvt
                .as_ref()
                .filter(|_| cx.options.use_lvt_names)
                .map(|local| local.get_name())
        })
        .or_else(|| processor.and_then(|proc| proc.names.get(&pair).and_then(Option::as_ref)))
        .map_or(fallback.as_str(), ArcStr::as_str);
    let this_class = processor.and_then(|proc| proc.this_vars.get(&pair));

    if let Some(method) = cx.writing_method()
        && (name != "this" || variable.index != 0)
    {
        let (method, index) = token_source(cx, method, &variable)?;
        let descriptor = MethodDescriptor::parse_descriptor(&method.method.descriptor);
        let slot = cx.ir[method.variables]
            .versions
            .original
            .get(&index)
            .map_or(index, |pair| pair.var);
        let params_size: i32 = descriptor.params.iter().map(|ty| ty.stack_size).sum();
        let parameter = slot <= params_size - i32::from(method.method.has_modifier(ACC_STATIC));
        if let Some((owner, class, receiver)) = qualified_receiver(this_class, name) {
            buffer.append_class(class, false, owner).append_char('.');
            write_name(&mut buffer, receiver, &fallback);
        } else {
            let visible = if valid_name(name) || name.contains(".this") {
                name
            } else {
                &fallback
            };
            buffer.append_variable(
                visible,
                variable.definition,
                parameter,
                &method.method.class_qualified_name,
                &method.method.name,
                descriptor,
                index,
                name,
            );
            append_original_name(&mut buffer, name, visible);
        }
    } else if let Some((owner, class, receiver)) = qualified_receiver(this_class, name) {
        buffer.append_class(class, false, owner).append_char('.');
        write_name(&mut buffer, receiver, &fallback);
    } else {
        write_name(&mut buffer, name, &fallback);
    }
    Ok(buffer)
}

pub(crate) fn definition_type(cx: &Cx, expr: ExprId, variable: &Variable) -> VarType {
    if cx.options.use_lvt_names
        && variable.lvt.is_none()
        && let Some(owner) = variable.processor
        && let Some(pair) = cx.ir[owner].versions.original.get(&variable.index)
        && let Some(method) = cx.writing_method().map(|wrapper| &wrapper.method)
    {
        let offset = cx.ir[expr]
            .bytecode
            .as_ref()
            .map_or(-1, |offsets| offsets.length());
        let erased = method
            .get_local_variable_attr()
            .and_then(|lvt| lvt.get_descriptor(pair.var, offset))
            .map(|descriptor| VarType::from_signature(descriptor));
        if cx.options.decompile_generics
            && let Some(signature) = method
                .attributes
                .local_variable_type_table
                .as_ref()
                .and_then(|lvtt| lvtt.get_signature(pair.var, offset))
            && let Some(mut generic) = generic_main::parse_field_signature(signature)
        {
            if let Some(ty) = &erased {
                generic.verify_loosely(cx, ty);
            }
            return generic.ty;
        }
        if let Some(ty) = erased {
            return ty;
        }
    }
    variable.definition_var_type(cx)
}

fn token_source<'a>(
    cx: &'a Cx,
    mut method: &'a MethodWrapper,
    variable: &Variable,
) -> io::Result<(&'a MethodWrapper, i32)> {
    let mut index = variable.index;
    if let Some(processor) = variable.processor
        && let Some(node) = cx
            .current_class_node
            .as_deref()
            .and_then(|name| cx.class_nodes.id(name))
    {
        let mut source = cx.ir[processor].sources.get(&variable.pair());
        while let Some((key, pair)) = source {
            method = cx
                .method_wrapper_by_key(node, key)
                .ok_or_else(|| invalid("Missing enclosing method for a captured variable"))?;
            index = pair.var;
            source = cx.ir[method.variables].sources.get(pair);
        }
    }
    Ok((method, index))
}

fn qualified_receiver<'a, 'b>(
    this_class: Option<&'a ArcStr>,
    name: &'b str,
) -> Option<(&'a str, &'b str, &'b str)> {
    let owner = this_class?;
    let dot = name.find(".this")?;
    Some((owner.as_str(), &name[..dot], &name[dot + 1..]))
}

fn valid_name(name: &str) -> bool {
    name.is_empty() || name == NAMELESS_ENCLOSURE || is_java_identifier(name)
}

fn write_name(buffer: &mut TextBuffer, name: &str, fallback: &str) {
    let visible = if valid_name(name) { name } else { fallback };
    buffer.append(visible);
    append_original_name(buffer, name, visible);
}

fn append_original_name(buffer: &mut TextBuffer, name: &str, displayed: &str) {
    if name != displayed {
        buffer.append("/* $VF was: ").append(name).append(" */");
    }
}

fn invalid(message: &str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}
