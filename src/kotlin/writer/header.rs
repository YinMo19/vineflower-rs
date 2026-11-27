use std::io;

use crate::{
    engine::{Cx, class_writer::annotations::declaration_annotations},
    kotlin::{identifier, imports, members::ClassElement},
    structs::StructClass,
    util::{java_str::JavaString, text_buffer::TextBuffer},
};

use super::annotations::{self, UseSiteTarget};

/// Write the package, file annotations, imports and class type aliases once
/// all source references in the compilation unit have resolved their names.
pub fn write_header(cx: &mut Cx, class: &StructClass, buffer: &mut TextBuffer) -> io::Result<()> {
    let package = class
        .qualified_name
        .rsplit_once('/')
        .map(|(package, _)| package);
    let element = cx
        .kotlin_members()
        .and_then(|members| members.class(class))
        .cloned();
    if let Some(ClassElement::File(file)) = &element {
        if let Some(facade) = &file.multifile_name {
            let name = facade_name(package, facade)?;
            buffer
                .append("@file:JvmMultifileClass")
                .append_line_separator()
                .append("@file:JvmName(\"")
                .append(&name)
                .append("\")")
                .append_line_separator();
        }
        for annotation in
            declaration_annotations(&class.attributes).filter(|a| a.class_name != "kotlin/Metadata")
        {
            buffer
                .append_buffer(&annotations::render(
                    cx,
                    annotation,
                    0,
                    Some(UseSiteTarget::File),
                )?)
                .append_line_separator();
        }
        if !buffer.contains_only_whitespaces() {
            buffer.append_line_separator();
        }
    }
    if let Some(package) = package {
        buffer.append("package ");
        for (index, part) in crate::util::java_str::split(package, "/")
            .into_iter()
            .enumerate()
        {
            if index > 0 {
                buffer.append_char('.');
            }
            buffer.append(&identifier(part));
        }
        buffer.append_line_separator().append_line_separator();
    }
    imports::write_imports(cx, buffer, true);
    if let Some(ClassElement::Class(class)) = &element
        && !class.proto.type_alias.is_empty()
    {
        let names = class
            .names
            .as_ref()
            .ok_or_else(|| io::Error::other("Missing Kotlin type alias name resolver"))?;
        let resolve = |idx| crate::kotlin::declarations::resolve(names, idx);
        for alias in &class.proto.type_alias {
            let name = resolve(alias.name())?;
            let underlying = resolve(
                alias
                    .underlying_type
                    .as_ref()
                    .map_or(0, |ty| ty.class_name()),
            )?;
            buffer
                .append("typealias ")
                .append(&identifier(&name))
                .append(" = ")
                .append(&identifier(&underlying))
                .append_line_separator();
        }
        buffer.append_line_separator();
    }
    Ok(())
}

fn facade_name(package: Option<&str>, facade: &JavaString) -> io::Result<String> {
    let raw = facade.as_utf8_lossy();
    let Some(package) = package.filter(|package| raw.starts_with(package)) else {
        return Ok(raw.to_string());
    };
    // The Java writer removes the package and one UTF-16 separator character.
    let mut units = facade.utf16().skip(package.encode_utf16().count());
    units
        .next()
        .ok_or_else(|| io::Error::other("Kotlin multifile facade name ends at its package"))?;
    Ok(String::from_utf16_lossy(&units.collect::<Vec<_>>()))
}
