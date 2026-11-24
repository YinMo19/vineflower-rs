// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.

use std::{borrow::Cow, collections::HashMap};

use crate::{
    Options, bytecode,
    classfile::{ClassFile, Member},
    context::ClassGroup,
    descriptor::{MethodDescriptor, Primitive, Type as JvmType},
    emit::SourceMap,
};

use super::{
    Bytecode, KotlinError, error, identifier, qualified,
    trace::{Trace, line_count},
};
use crate::kotlin::{
    Declaration,
    body::{ABSTRACT, NATIVE, STATIC, load_opcode, local_load, return_opcode},
    read_metadata,
};

pub(super) fn package_part_facade<'a>(
    owner: &'a str,
    extra: Option<&'a str>,
    group: Option<&ClassGroup<'_>>,
) -> Result<Cow<'a, str>, KotlinError> {
    let facade = match extra.filter(|name| !name.is_empty()) {
        Some(name) if !name.contains('/') && !package(owner).is_empty() => {
            Cow::Owned(format!("{}/{name}", package(owner)))
        }
        Some(name) => Cow::Borrowed(name),
        None => {
            let name = simple_name(owner);
            let (facade, _) = name
                .split_once("__")
                .ok_or_else(|| error(owner, "multifile part has no facade name"))?;
            Cow::Borrowed(&owner[..owner.len() - name.len() + facade.len()])
        }
    };
    if !internal_name(&facade) || facade == owner || package(&facade) != package(owner) {
        return Err(error(owner, "invalid multifile facade name"));
    }
    if let Some(class) = group.and_then(|group| group.get(&facade)) {
        let metadata = read_metadata(class)?
            .ok_or_else(|| error(owner, "multifile facade lacks Kotlin metadata"))?;
        if !matches!(metadata.declaration, Declaration::MultifileFacade(parts) if parts.iter().any(|name| name == owner))
        {
            return Err(error(
                owner,
                "multifile facade does not claim its package part",
            ));
        }
    }
    Ok(facade)
}

pub(super) fn render(
    out: &mut String,
    bytecode: &Bytecode<'_, '_>,
    simple: &str,
    parts: &[String],
    group: Option<&ClassGroup<'_>>,
    options: Option<&Options>,
    mut mapping: Option<&mut SourceMap>,
) -> Result<(), KotlinError> {
    let owner = bytecode.owner;
    let enabled = options.is_some_and(|options| options.decompile_kotlin_facades);
    let mut available = HashMap::with_capacity(parts.len());
    if parts.is_empty() {
        return Err(error(owner, "multifile facade has no package parts"));
    }
    out.push_str("/*\n * This is a multifile facade. The actual implementations of the functions are in the following files:\n");
    for part in parts {
        if part == owner || !internal_name(part) || package(part) != package(owner) {
            return Err(error(owner, "invalid multifile package part name"));
        }
        let linked = group.and_then(|group| group.get(part));
        if available.insert(part.as_str(), linked).is_some() {
            return Err(error(owner, "duplicate multifile package part"));
        }
        if let Some(class) = linked {
            let metadata = read_metadata(class)?
                .ok_or_else(|| error(part, "multifile part lacks Kotlin metadata"))?;
            if !matches!(metadata.declaration, Declaration::MultifilePart(_))
                || package_part_facade(part, metadata.header.extra_string.as_deref(), None)?
                    != owner
            {
                return Err(error(
                    part,
                    "multifile package part belongs to another facade",
                ));
            }
        }
        out.push_str(" * ");
        out.push_str(part);
        out.push('\n');
    }
    out.push_str(" */\n");
    if !enabled {
        return Ok(());
    }
    if !bytecode.class.fields.is_empty() {
        return Err(error(owner, "multifile facade fields"));
    }
    let options = options.expect("facade wrappers require the enabled option");
    out.push_str("internal class ");
    identifier(out, simple, owner)?;
    let mut line = line_count(out) + 1;
    let mut any = false;
    for method in &bytecode.class.methods {
        if options.remove_synthetic && method.access_flags & 0x1000 != 0
            || options.remove_bridge && method.access_flags & 0x0040 != 0
        {
            continue;
        }
        if any {
            out.push('\n');
            line += 1;
        } else {
            out.push_str(" {\n");
            any = true;
        }
        render_wrapper(
            out,
            bytecode,
            method,
            &available,
            options,
            line,
            mapping.as_deref_mut(),
        )?;
        line += 4;
    }
    out.push_str(if any { "}\n" } else { "\n" });
    Ok(())
}

fn render_wrapper<'data>(
    out: &mut String,
    bytecode: &Bytecode<'_, 'data>,
    member: &Member<'data>,
    available: &HashMap<&str, Option<&ClassFile<'_>>>,
    options: &Options,
    line: usize,
    mapping: Option<&mut SourceMap>,
) -> Result<(), KotlinError> {
    let pool = &bytecode.class.pool;
    let name = pool.utf8(member.name_index)?;
    let raw_descriptor = pool.utf8(member.descriptor_index)?;
    let invalid = || error(name, "not a direct Kotlin multifile forwarding method");
    if member.access_flags & (STATIC | ABSTRACT | NATIVE) != STATIC
        || member.signature(pool)?.is_some()
    {
        return Err(invalid());
    }
    let descriptor = MethodDescriptor::parse(raw_descriptor)?;
    let code = bytecode.code(member, name)?;
    let instructions = bytecode::decode(code.bytes)?;
    let [loads @ .., invoke, ret] = instructions.as_slice() else {
        return Err(invalid());
    };
    let (target, called, called_descriptor) =
        bytecode.reference(invoke, 0xb8)?.ok_or_else(invalid)?;
    let linked = available.get(target).ok_or_else(invalid)?;
    if called != name
        || called_descriptor != raw_descriptor
        || ret.opcode != return_opcode(&descriptor.return_type)
        || loads.len() != descriptor.parameters.len()
    {
        return Err(invalid());
    }
    if let Some(part) = linked {
        let mut found = false;
        for target_method in &part.methods {
            if part.pool.utf8(target_method.name_index)? == called
                && part.pool.utf8(target_method.descriptor_index)? == called_descriptor
                && target_method.access_flags & STATIC != 0
            {
                found = true;
                break;
            }
        }
        if !found {
            return Err(error(
                name,
                "multifile forwarding target is absent from its package part",
            ));
        }
    }
    let mut slot = 0;
    for (load, parameter) in loads.iter().zip(&descriptor.parameters) {
        if local_load(load) != Some((load_opcode(parameter), slot)) {
            return Err(invalid());
        }
        slot += parameter.slots();
    }

    let method_parameters = if options.use_method_parameters {
        member.method_parameters(pool)?
    } else {
        Vec::new()
    };
    let debug_locals = if options.use_debug_names && !loads.is_empty() {
        code.local_variables(pool)?
    } else {
        Vec::new()
    };
    let parameter_names = loads
        .iter()
        .enumerate()
        .map(|(index, load)| {
            let (_, slot) = local_load(load).expect("forwarding argument validated");
            if let Some(index) = method_parameters
                .get(index)
                .map(|parameter| parameter.name_index)
                .filter(|&index| index != 0)
            {
                return Ok(Cow::Borrowed(pool.utf8(index)?));
            }
            if let Some(local) = debug_locals
                .iter()
                .find(|local| local.index == slot && local.start_pc == 0)
            {
                return Ok(Cow::Borrowed(local.name));
            }
            Ok(Cow::Owned(format!("var{slot}")))
        })
        .collect::<Result<Vec<_>, KotlinError>>()?;

    let indent = &options.indent;
    out.push_str(indent);
    out.push_str("@JvmStatic\n");
    out.push_str(indent);
    out.push_str("fun ");
    identifier(out, name, name)?;
    out.push('(');
    for (index, (parameter, ty)) in parameter_names
        .iter()
        .zip(&descriptor.parameters)
        .enumerate()
    {
        if index != 0 {
            out.push_str(", ");
        }
        identifier(out, parameter, name)?;
        out.push_str(": ");
        wrapper_type(out, ty, name)?;
    }
    out.push(')');
    if descriptor.return_type != JvmType::Void {
        out.push_str(": ");
        wrapper_type(out, &descriptor.return_type, name)?;
    }
    out.push_str(" {\n");
    out.push_str(indent);
    out.push_str(indent);
    if descriptor.return_type != JvmType::Void {
        out.push_str("return ");
    }
    identifier(out, simple_name(target), name)?;
    out.push('.');
    identifier(out, called, name)?;
    out.push('(');
    for (index, parameter) in parameter_names.iter().enumerate() {
        if index != 0 {
            out.push_str(", ");
        }
        identifier(out, parameter, name)?;
    }
    out.push_str(")\n");
    out.push_str(indent);
    out.push_str("}\n");
    if let Some(mapping) = mapping {
        let mut trace = Trace::new(bytecode, member)?;
        for instruction in loads.iter().chain([invoke]) {
            trace.instruction(instruction, line + 2);
        }
        trace.instruction(ret, line + 3);
        trace.finish(mapping, code.line_numbers(pool)?);
    }
    Ok(())
}

fn wrapper_type(out: &mut String, ty: &JvmType, declaration: &str) -> Result<(), KotlinError> {
    match ty {
        JvmType::Primitive(primitive) => out.push_str(primitive_name(*primitive)),
        JvmType::Array(element) => {
            if let JvmType::Primitive(primitive) = **element {
                out.push_str(primitive_name(primitive));
                out.push_str("Array");
            } else {
                out.push_str("Array<");
                wrapper_type(out, element, declaration)?;
                out.push('>');
            }
        }
        JvmType::Object(name) => match name.as_str() {
            "java/lang/Object" => out.push_str("Any"),
            "java/lang/String" => out.push_str("String"),
            "java/lang/CharSequence" => out.push_str("CharSequence"),
            "kotlin/Unit" => out.push_str("Unit"),
            _ => qualified(out, name, declaration)?,
        },
        JvmType::Void => return Err(error(declaration, "void forwarding parameter")),
    }
    Ok(())
}

fn primitive_name(primitive: Primitive) -> &'static str {
    match primitive {
        Primitive::Boolean => "Boolean",
        Primitive::Byte => "Byte",
        Primitive::Char => "Char",
        Primitive::Short => "Short",
        Primitive::Int => "Int",
        Primitive::Long => "Long",
        Primitive::Float => "Float",
        Primitive::Double => "Double",
    }
}

pub(super) fn simple_name(name: &str) -> &str {
    name.rsplit_once('/').map_or(name, |(_, simple)| simple)
}
fn package(name: &str) -> &str {
    name.rsplit_once('/').map_or("", |(package, _)| package)
}

fn internal_name(name: &str) -> bool {
    !name.contains("*/")
        && !name.chars().any(|c| {
            c.is_control() || matches!(c, '.' | ';' | '[' | '\\' | '\u{2028}' | '\u{2029}')
        })
        && name.split('/').all(|component| !component.is_empty())
}
