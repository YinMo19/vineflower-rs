//! Method error comments and bytecode listings.

use std::error::Error;
use std::fmt::Write;
use std::io;

use super::comments::error_comment;
use crate::code::code_constants::{
    CONSTANT_DYNAMIC, CONSTANT_STRING, GROUP_FIELDACCESS, GROUP_INVOCATION, GROUP_JUMP,
    OPC_CHECKCAST, OPC_INSTANCEOF, OPC_INVOKEDYNAMIC, OPC_LDC, OPC_LDC_W, OPC_LDC2_W, OPC_NEW,
};
use crate::decompiler::exps::literal::escape_string;
use crate::engine::{
    Cx,
    class_wrapper::{MethodWrapper, catch_method_failure},
};
use crate::structs::{
    StructClass, StructMethod,
    attr::StructBootstrapMethodsAttribute,
    consts::{LinkConstant, PooledConstant},
};
use crate::util::{text_buffer::TextBuffer, text_util::get_instruction_name};

pub(super) fn dump_error(
    cx: &Cx,
    buffer: &mut TextBuffer,
    owner: &StructClass,
    wrapper: &MethodWrapper,
    indent: i32,
) {
    dump_method_error(cx, buffer, owner, wrapper, indent, true);
}

/// The Java bytecode listing includes exception handlers after the instructions.
pub(crate) fn dump_method_error(
    cx: &Cx,
    buffer: &mut TextBuffer,
    owner: &StructClass,
    wrapper: &MethodWrapper,
    indent: i32,
    include_handlers: bool,
) {
    let mut lines = vec!["$VF: Couldn't be decompiled".to_owned()];
    if cx.options.dump_exception_on_error {
        lines.extend(error_comment(&cx.options.error_message).map(str::to_owned));
        if let Some(error) = wrapper.decompile_error() {
            append_error_lines(&mut lines, error);
        }
        if cx.options.dump_bytecode_on_error {
            lines.push(String::new());
        }
    }
    if cx.options.dump_bytecode_on_error {
        lines.push("Bytecode:".to_owned());
        if let Err(error) = catch_method_failure(|| {
            collect_bytecode(owner, &wrapper.method, &mut lines, include_handlers)
        }) {
            lines.push("Error collecting bytecode:".to_owned());
            append_error_lines(&mut lines, &error);
        }
    }
    for line in lines {
        append_error_comment(buffer, &line, indent);
    }
}

pub(crate) fn write_exception(cx: &Cx, buffer: &mut TextBuffer, error: &dyn Error) {
    append_error_comment(buffer, "$VF: Couldn't be decompiled", 0);
    if cx.options.dump_exception_on_error {
        for line in exception_details(cx, error) {
            append_error_comment(buffer, &line, 0);
        }
    }
}

pub(crate) fn exception_details(cx: &Cx, error: &dyn Error) -> Vec<String> {
    let mut lines: Vec<_> = error_comment(&cx.options.error_message)
        .map(str::to_owned)
        .collect();
    append_error_lines(&mut lines, error);
    lines
}

pub(crate) fn write_class_error(cx: &Cx, buffer: &mut TextBuffer, error: &dyn Error) {
    buffer
        .append("/*")
        .append_line_separator()
        .append("$VF: Unable to decompile class")
        .append_line_separator();
    for line in exception_details(cx, error) {
        buffer.append(&line).append_line_separator();
    }
    buffer.append("*/");
}

fn append_error_comment(buffer: &mut TextBuffer, line: &str, indent: i32) {
    buffer.append_indent(indent).append("//");
    if !line.is_empty() {
        buffer.append_char(' ').append(line);
    }
    buffer.append_line_separator();
}

fn append_error_lines(lines: &mut Vec<String>, error: &dyn Error) {
    lines.push(error.to_string());
    let mut cause = error.source();
    while let Some(error) = cause {
        lines.push(format!("Caused by: {error}"));
        cause = error.source();
    }
}

fn collect_bytecode(
    owner: &StructClass,
    method: &StructMethod,
    lines: &mut Vec<String>,
    include_handlers: bool,
) -> io::Result<()> {
    let instructions = method
        .expand_data(owner)?
        .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "Method has no code"))?;
    let last_offset = instructions
        .instructions
        .last()
        .map_or(0, |instruction| instruction.start_offset);
    let width = (8 - last_offset.leading_zeros() / 4) as usize;
    let pool = &owner.pool;
    let bootstrap = owner.attributes.bootstrap_methods.as_ref();
    for instruction in &instructions {
        let start = instruction.start_offset;
        let mut line = format!("{start:0width$x}: ");
        if instruction.wide {
            line.push_str("wide ");
        }
        line.push_str(get_instruction_name(instruction.opcode));
        match instruction.group {
            GROUP_INVOCATION => {
                line.push(' ');
                let constant = pool.get_constant(instruction.operand(0));
                if instruction.opcode == OPC_INVOKEDYNAMIC
                    && let Some(bootstrap) = bootstrap
                    && let Some(PooledConstant::Link(target)) = constant
                {
                    append_bootstrap_call(&mut line, target, bootstrap);
                } else {
                    append_constant(&mut line, constant);
                }
                for i in 1..instruction.operands_count() {
                    write!(line, " {}", instruction.operand(i)).unwrap();
                }
            }
            GROUP_FIELDACCESS => {
                line.push(' ');
                append_constant(&mut line, pool.get_constant(instruction.operand(0)));
            }
            GROUP_JUMP => {
                let destination = start.wrapping_add(instruction.operand(0));
                write!(line, " {destination:0width$x}").unwrap();
            }
            _ if matches!(
                instruction.opcode,
                OPC_NEW | OPC_CHECKCAST | OPC_INSTANCEOF | OPC_LDC | OPC_LDC_W | OPC_LDC2_W
            ) =>
            {
                line.push(' ');
                let constant = pool.get_constant(instruction.operand(0));
                if let Some(PooledConstant::Link(target)) = constant
                    && target.ty == CONSTANT_DYNAMIC
                    && let Some(bootstrap) = bootstrap
                {
                    append_bootstrap_call(&mut line, target, bootstrap);
                } else {
                    append_constant(&mut line, constant);
                }
            }
            _ => {
                for i in 0..instruction.operands_count() {
                    write!(line, " {}", instruction.operand(i)).unwrap();
                }
            }
        }
        lines.push(line);
    }
    if !include_handlers {
        return Ok(());
    }
    for handler in &instructions.exception_table.handlers {
        lines.push(format!(
            "try ({} -> {}): {} {}",
            handler.from,
            handler.to,
            handler.handler,
            handler.exception_class.as_deref().unwrap_or("null")
        ));
    }
    Ok(())
}

fn append_bootstrap_call(
    line: &mut String,
    target: &LinkConstant,
    bootstrap: &StructBootstrapMethodsAttribute,
) {
    write!(line, "{} {} bsm=", target.elementname, target.descriptor).unwrap();
    append_link_constant(line, bootstrap.get_method_reference(target.index1));
    line.push_str(" args=[ ");
    for (i, argument) in bootstrap
        .get_method_arguments(target.index1)
        .iter()
        .enumerate()
    {
        if i > 0 {
            line.push_str(", ");
        }
        append_constant(line, argument.as_ref());
    }
    line.push_str(" ]");
}

fn append_constant(line: &mut String, constant: Option<&PooledConstant>) {
    match constant {
        None => line.push_str("<null constant>"),
        Some(PooledConstant::Link(link)) => append_link_constant(line, link),
        Some(PooledConstant::Primitive(primitive)) if primitive.ty == CONSTANT_STRING => {
            line.push('"');
            line.push_str(&escape_string(primitive.get_java_string(), false));
            line.push('"');
        }
        Some(PooledConstant::Primitive(primitive)) => {
            let value = primitive.value.java_string();
            line.push_str(value.as_ref().map_or("null", |value| value.as_utf8_lossy()));
        }
    }
}

fn append_link_constant(line: &mut String, link: &LinkConstant) {
    write!(
        line,
        "{}.{} {}",
        link.classname.as_deref().unwrap_or("null"),
        link.elementname,
        link.descriptor,
    )
    .unwrap();
}
