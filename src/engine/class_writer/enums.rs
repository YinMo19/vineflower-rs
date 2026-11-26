// Copyright 2000-2020 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Enum preparation before writing the class body.

use std::{io, sync::Arc};

use super::initializers::{constructor_call, first_data};
use crate::code::code_constants::INIT_NAME;
use crate::engine::Cx;
use crate::engine::class_nodes::ClassNodeId;
use crate::engine::class_wrapper::MethodSlot;
use crate::structs::StructMember;
use crate::util::interpreter_util::make_unique_key;

/// `EnumProcessor.clearEnum`. The caller has selected a published enum wrapper.
pub(super) fn clear_enum(cx: &mut Cx, node: ClassNodeId) -> io::Result<()> {
    let class = Arc::clone(&cx.class_nodes[node].class);
    let enum_array = format!("[L{};", class.qualified_name);
    let values = format!("(){enum_array}");
    let value_of = format!("(Ljava/lang/String;)L{};", class.qualified_name);

    for (index, declaration) in class.methods.iter().enumerate() {
        let method = MethodSlot { node, index };
        let name = declaration.name.as_str();
        let descriptor = declaration.descriptor.as_str();
        match (name, descriptor) {
            ("values", d) if d == values => {
                cx.class_nodes[node]
                    .hidden_members
                    .insert(make_unique_key(name, descriptor));
            }
            ("valueOf", d) if d == value_of => {
                cx.class_nodes[node]
                    .hidden_members
                    .insert(make_unique_key(name, descriptor));
            }
            (INIT_NAME, _) => {
                let root = method.get(cx).root().ok_or_else(|| {
                    io::Error::new(
                        io::ErrorKind::InvalidData,
                        "Enum constructor has no statement root",
                    )
                })?;
                if let Some(list) = first_data(&cx.ir, root)
                    && let Some(&expr) = cx.ir[list].first()
                    && constructor_call(cx, method, &class, expr, false)
                {
                    cx.ir[list].remove(0);
                }
            }
            _ => {}
        }
    }

    cx.class_nodes[node].hidden_members.extend(
        class
            .fields
            .iter()
            .filter(|field| field.is_synthetic() && field.descriptor.as_str() == enum_array)
            .map(|field| make_unique_key(&field.name, &field.descriptor)),
    );
    Ok(())
}
