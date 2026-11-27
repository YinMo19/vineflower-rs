//! Java source carried by package-info and module-info class files.

use std::io;

use arcstr::ArcStr;

use crate::code::code_constants::{
    ACC_MANDATED, ACC_OPEN, ACC_STATIC_PHASE, ACC_SYNTHETIC, ACC_TRANSITIVE,
};
use crate::engine::{Cx, import_collector::java_class_name};
use crate::structs::{StructClass, attr::StructModuleAttribute};
use crate::util::text_buffer::TextBuffer;

use super::annotations::append_annotations;

pub(in crate::engine) fn package_info_to_java(
    cx: &mut Cx,
    class: &StructClass,
    buffer: &mut TextBuffer,
) -> io::Result<()> {
    append_annotations(cx, buffer, &class.attributes, 0, -1)?;
    let (package, _) = class.qualified_name.rsplit_once('/').ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            "package-info has no package name",
        )
    })?;
    buffer
        .append("package ")
        .append(&package.replace('/', "."))
        .append_char(';')
        .append_line_separator()
        .append_line_separator();
    Ok(())
}

pub(in crate::engine) fn module_info_to_java(
    cx: &mut Cx,
    class: &StructClass,
    module: &StructModuleAttribute,
    buffer: &mut TextBuffer,
) -> io::Result<()> {
    append_annotations(cx, buffer, &class.attributes, 0, -1)?;
    if module.module_flags & ACC_OPEN != 0 {
        buffer.append("open ");
    }
    buffer
        .append("module ")
        .append(&module.module_name)
        .append(" {")
        .append_line_separator();
    module_body(cx, buffer, module);
    buffer.append_char('}').append_line_separator();
    Ok(())
}

fn module_body(cx: &Cx, buffer: &mut TextBuffer, module: &StructModuleAttribute) {
    let mut wrote_section = false;
    for entry in &module.requires {
        if generated(entry.flags) {
            continue;
        }
        buffer.append_indent(1).append("requires ");
        if entry.flags & ACC_TRANSITIVE != 0 {
            buffer.append("transitive ");
        }
        if entry.flags & ACC_STATIC_PHASE != 0 {
            buffer.append("static ");
        }
        buffer
            .append(&entry.module_name.replace('/', "."))
            .append_char(';')
            .append_line_separator();
        wrote_section = true;
    }

    append_package_directives(
        buffer,
        "exports",
        module.exports.iter().map(|entry| {
            (
                entry.package_name.as_str(),
                entry.flags,
                entry.export_to_modules.as_slice(),
            )
        }),
        &mut wrote_section,
    );
    append_package_directives(
        buffer,
        "opens",
        module.opens.iter().map(|entry| {
            (
                entry.package_name.as_str(),
                entry.flags,
                entry.opens_to_modules.as_slice(),
            )
        }),
        &mut wrote_section,
    );

    if !module.uses.is_empty() {
        if wrote_section {
            buffer.append_line_separator();
        }
        for service in &module.uses {
            buffer
                .append_indent(1)
                .append("uses ")
                .append(&java_class_name(cx, service))
                .append_char(';')
                .append_line_separator();
        }
        wrote_section = true;
    }

    if !module.provides.is_empty() {
        if wrote_section {
            buffer.append_line_separator();
        }
        for service in &module.provides {
            buffer
                .append_indent(1)
                .append("provides ")
                .append(&java_class_name(cx, &service.interface_name))
                .append(" with")
                .append_line_separator();
            append_names(
                buffer,
                service
                    .implementation_names
                    .iter()
                    .map(|name| java_class_name(cx, name)),
            );
            buffer.append_char(';').append_line_separator();
        }
    }
}

fn append_package_directives<'a>(
    buffer: &mut TextBuffer,
    directive: &str,
    entries: impl ExactSizeIterator<Item = (&'a str, i32, &'a [ArcStr])>,
    wrote_section: &mut bool,
) {
    if entries.len() != 0 && *wrote_section {
        buffer.append_line_separator();
    }
    for (package, flags, targets) in entries {
        if generated(flags) {
            continue;
        }
        buffer
            .append_indent(1)
            .append(directive)
            .append_char(' ')
            .append(&package.replace('/', "."));
        if !targets.is_empty() {
            buffer.append(" to").append_line_separator();
            append_names(buffer, targets.iter().map(ArcStr::as_str));
        }
        buffer.append_char(';').append_line_separator();
        *wrote_section = true;
    }
}

fn append_names(buffer: &mut TextBuffer, names: impl ExactSizeIterator<Item = impl AsRef<str>>) {
    let count = names.len();
    for (index, name) in names.enumerate() {
        buffer.append_indent(2).append(name.as_ref());
        if index + 1 < count {
            buffer.append_char(',').append_line_separator();
        }
    }
}

fn generated(flags: i32) -> bool {
    flags & (ACC_SYNTHETIC | ACC_MANDATED) != 0
}
