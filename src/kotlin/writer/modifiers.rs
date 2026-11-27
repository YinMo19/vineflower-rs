use std::io;

use crate::{
    code::code_constants::*, decompiler::expr_processor::get_cast_type_name, engine::Cx,
    types::VarType, util::text_buffer::TextBuffer,
};

pub const CLASS_ALLOWED: i32 = ACC_PROTECTED | ACC_PRIVATE | ACC_ABSTRACT | ACC_STATIC | ACC_STRICT;
pub const CLASS_EXCLUDED: i32 = ACC_ABSTRACT | ACC_STATIC;

pub(super) const FIELD_ALLOWED: i32 = ACC_PUBLIC
    | ACC_PROTECTED
    | ACC_PRIVATE
    | ACC_STATIC
    | ACC_FINAL
    | ACC_TRANSIENT
    | ACC_VOLATILE;
pub(super) const FIELD_EXCLUDED: i32 = ACC_PUBLIC | ACC_STATIC | ACC_FINAL;

pub fn append_modifiers(
    buffer: &mut TextBuffer,
    flags: i32,
    allowed: i32,
    is_interface: bool,
    excluded: i32,
) {
    let flags = flags & allowed & !(if is_interface { excluded } else { 0 });
    for (flag, name) in [
        (ACC_PUBLIC, "public"),
        (ACC_PROTECTED, "protected"),
        (ACC_PRIVATE, "private"),
        (ACC_ABSTRACT, "abstract"),
        (ACC_NATIVE, "native"),
    ] {
        if flags & flag != 0 {
            buffer.append(name).append_char(' ');
        }
    }
}

pub fn append_type_parameters(
    cx: &mut Cx,
    buffer: &mut TextBuffer,
    names: &[String],
    bounds: &[Vec<VarType>],
) -> io::Result<()> {
    buffer.append_char('<');
    for (index, name) in names.iter().enumerate() {
        if index > 0 {
            buffer.append(", ");
        }
        buffer.append(name);
        let Some([first, rest @ ..]) = bounds.get(index).map(Vec::as_slice) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "Missing Kotlin type parameter bound",
            ));
        };
        if !rest.is_empty() || first.value.as_deref() != Some("java/lang/Object") {
            buffer
                .append(" extends ")
                .append(&get_cast_type_name(cx, first));
            for bound in rest {
                buffer.append(" & ").append(&get_cast_type_name(cx, bound));
            }
        }
    }
    buffer.append_char('>');
    Ok(())
}
