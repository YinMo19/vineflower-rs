//! Shared helpers from ExprUtil.

use std::io;

use super::Invocation;
use crate::code::code_constants::{ACC_STATIC, INIT_NAME};
use crate::decompiler::vars::var_version_pair::VarVersionPair;
use crate::engine::Cx;
use crate::engine::class_nodes::ClassKind;
use crate::structs::{StructClass, StructMember};
use crate::util::interpreter_util::make_unique_key;

/// The mask is indexed by JVM parameter, including captured and enum arguments.
pub(crate) fn visible_parameters(
    mask: Option<&[Option<VarVersionPair>]>,
) -> impl Fn(usize) -> bool {
    move |index| mask.is_none_or(|slots| slots[index].is_none())
}

pub(crate) fn synthetic_parameters_mask(
    cx: &Cx,
    call: &Invocation,
) -> io::Result<Option<Vec<Option<VarVersionPair>>>> {
    let Some(node) = call
        .classname
        .as_deref()
        .and_then(|name| cx.class_nodes.id(name))
    else {
        return Ok(None);
    };
    let class_node = &cx.class_nodes[node];
    if let Some(owner) = cx
        .class_nodes
        .wrapper_owner(node)
        .map(|owner| &cx.class_nodes[owner])
        && let Some(wrapper) = &owner.wrapper
    {
        let key = make_unique_key(INIT_NAME, call.string_descriptor());
        if let Some(index) = owner.class.methods.index_of_key(&key) {
            return Ok(wrapper.methods[index].synthetic_parameters.clone());
        }
        if !cx.options.ignore_invalid_bytecode {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "Constructor {}.<init>{} not found",
                    class_node.class.qualified_name,
                    call.string_descriptor()
                ),
            ));
        }
    } else if !call.parameters.is_empty()
        && class_node.kind == ClassKind::Member
        && !is_static_member(&class_node.class)
    {
        let mut mask = vec![None; call.parameters.len()];
        mask[0] = Some(VarVersionPair::new(-1, 0));
        return Ok(Some(mask));
    }
    Ok(None)
}

pub(crate) fn is_static_member(class: &StructClass) -> bool {
    class.has_modifier(ACC_STATIC)
        || class
            .attributes
            .inner_classes
            .as_ref()
            .and_then(|attribute| {
                attribute
                    .entries
                    .iter()
                    .find(|entry| entry.inner_name == class.qualified_name)
            })
            .is_some_and(|entry| entry.access_flags & ACC_STATIC != 0)
}
