use std::io;

use crate::{
    decompiler::{exps::literal::add_offsets, stats::StatementKind},
    engine::{
        Cx,
        class_nodes::ClassNodeId,
        class_wrapper::{MethodSlot, catch_method_failure},
        class_writer,
    },
    kotlin::body,
    util::{interpreter_util::make_unique_key, text_buffer::TextBuffer},
};

/// Render a published method under the caller's class and method context.
/// A lambda can have a different declaring class from its enclosing expression.
pub(crate) fn write_code(
    cx: &mut Cx,
    node: ClassNodeId,
    index: usize,
    buffer: &mut TextBuffer,
    indent: i32,
    hide_record_method: bool,
) -> io::Result<Option<bool>> {
    let slot = MethodSlot::at(node, index);
    let wrapper = slot.get(cx);
    let Some(root) = wrapper
        .root()
        .filter(|_| wrapper.decompile_error().is_none())
    else {
        return Ok(None);
    };
    let class = cx.class_nodes[node].class.clone();
    let method = wrapper.method.clone();
    let result = catch_method_failure(|| {
        if hide_record_method && class_writer::is_hidden_record_method(cx, &class, &method, root) {
            return Ok(None);
        }
        let mut code = body::statement(cx, root, indent)?;
        let StatementKind::Root { dummy_exit, .. } = cx.ir[root].kind else {
            unreachable!()
        };
        let StatementKind::DummyExit { ref bytecode } = cx.ir[dummy_exit].kind else {
            unreachable!()
        };
        add_offsets(&mut code, bytecode.as_ref());
        let key = make_unique_key(&method.name, &method.descriptor);
        buffer.append_buffer_for(&code, Some(&class.qualified_name), Some(&key));
        Ok(Some(code.length() != 0))
    });
    match result {
        Err(error) if error.kind() != io::ErrorKind::Interrupted => {
            log::warn!(
                "Method {} {} in class {} couldn't be written: {error}",
                method.name,
                method.descriptor,
                class.qualified_name
            );
            slot.record_write_error(cx, error);
            Ok(None)
        }
        result => result,
    }
}

pub(crate) fn dump_error(
    cx: &Cx,
    node: ClassNodeId,
    index: usize,
    buffer: &mut TextBuffer,
    indent: i32,
) {
    let class = cx.current_node().unwrap_or(node);
    let wrapper = MethodSlot::at(node, index).get(cx);
    class_writer::dump_method_error(
        cx,
        buffer,
        &cx.class_nodes[class].class,
        wrapper,
        indent,
        false,
    );
}

pub(crate) fn write_method_body(
    cx: &mut Cx,
    node: ClassNodeId,
    index: usize,
    buffer: &mut TextBuffer,
    indent: i32,
    hide_if_init: bool,
) -> io::Result<bool> {
    buffer.append_char('{').append_line_separator();
    let written = write_code(cx, node, index, buffer, indent + 1, true)?;
    if MethodSlot::at(node, index)
        .get(cx)
        .decompile_error()
        .is_some()
    {
        dump_error(cx, node, index, buffer, indent + 1);
    }
    buffer
        .append_indent(indent)
        .append_char('}')
        .append_line_separator();
    Ok(written.is_some_and(|has_code| has_code || !hide_if_init))
}
