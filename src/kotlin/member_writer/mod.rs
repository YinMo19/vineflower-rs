//! Source rendering for Kotlin functions, constructors, and properties.

mod constructors;
mod defaults;
mod functions;
mod properties;

pub use defaults::DefaultArgsMap;

use std::io;

use crate::engine::{Cx, class_nodes::ClassNodeId, class_wrapper::MethodSlot};
use crate::kotlin::{
    declarations::KParameter,
    members::DefaultArguments,
    metadata::{
        flags,
        proto::{Modality, Visibility},
    },
};
use crate::structs::StructMethod;
use crate::util::{interpreter_util::make_unique_key, text_buffer::TextBuffer};

fn invalid(message: impl Into<String>) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message.into())
}

fn method_slot(cx: &Cx, node: ClassNodeId, method: &StructMethod) -> io::Result<MethodSlot> {
    let key = make_unique_key(&method.name, &method.descriptor);
    MethodSlot::by_key(cx, node, &key)
        .ok_or_else(|| invalid(format!("Missing method wrapper for {key}")))
}

pub(crate) fn visibility(cx: &Cx, buffer: &mut TextBuffer, visibility: Visibility) {
    match visibility {
        Visibility::Local => {
            buffer
                .append("// $VF: local visibility outside of methodSupplier")
                .append_line_separator()
                .append("internal ");
        }
        Visibility::Private | Visibility::PrivateToThis => {
            buffer.append("private ");
        }
        Visibility::Public => {
            if cx.options.kt_show_public {
                buffer.append("public ");
            }
        }
        Visibility::Protected => {
            buffer.append("protected ");
        }
        Visibility::Internal => {
            buffer.append("internal ");
        }
    }
}

fn visibility_of(flags: i32) -> io::Result<Visibility> {
    flags::VISIBILITY
        .get(flags)
        .ok_or_else(|| invalid("Invalid Kotlin visibility"))
}

fn modality_word(modality: Modality) -> &'static str {
    match modality {
        Modality::Final => "final ",
        Modality::Open => "open ",
        Modality::Abstract => "abstract ",
        Modality::Sealed => "sealed ",
    }
}

fn modality_of(flags: i32) -> io::Result<Modality> {
    flags::MODALITY
        .get(flags)
        .ok_or_else(|| invalid("Invalid Kotlin modality"))
}

fn write_parameters(
    cx: &mut Cx,
    node: ClassNodeId,
    method: &StructMethod,
    parameters: &[KParameter],
    defaults: &DefaultArguments,
    buffer: &mut TextBuffer,
    indent: i32,
) -> io::Result<()> {
    let key = make_unique_key(&method.name, &method.descriptor);
    for (index, parameter) in parameters.iter().enumerate() {
        if index > 0 {
            buffer
                .append_char(',')
                .append_possible_newline_or(" ", false);
        }
        parameter.write(cx, buffer, indent + 1)?;
        if flags::DECLARES_DEFAULT_VALUE.get(parameter.flags) {
            let map = DefaultArgsMap::for_method(cx, node, method, parameters, defaults)?;
            let value = map.render_parameter(cx, index, indent + 1)?;
            buffer.append_buffer_for(&value, Some(&method.class_qualified_name), Some(&key));
        }
    }
    buffer
        .append_possible_newline_or("", true)
        .pop_newline_group();
    Ok(())
}

fn method_content(
    cx: &mut Cx,
    root: crate::decompiler::ir::StatId,
    indent: i32,
) -> io::Result<TextBuffer> {
    use crate::decompiler::{exps::literal, stats::StatementKind};
    let mut body = crate::kotlin::body::statement(cx, root, indent)?;
    let StatementKind::Root { dummy_exit, .. } = cx.ir[root].kind else {
        return Err(invalid("Kotlin method body is missing its root"));
    };
    let StatementKind::DummyExit { bytecode } = &cx.ir[dummy_exit].kind else {
        return Err(invalid("Kotlin method body is missing its dummy exit"));
    };
    literal::add_offsets(&mut body, bytecode.as_ref());
    Ok(body)
}
