// Copyright 2000-2020 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! The runtime-only fallback used by ClasspathHelper when the class path lacks an owner.

use crate::code::code_constants::{ACC_PUBLIC, ACC_VARARGS};
use crate::engine::Cx;
use crate::structs::StructMember;
use crate::types::{CodeType, MethodDescriptor};

pub(super) fn is_varargs(cx: &Cx, class: &str, name: &str, descriptor: &MethodDescriptor) -> bool {
    // The Java helper compares the qualified declaring name and descriptor
    // spelling to Method.toString(). Inherited declarations and primitive
    // descriptor letters cannot match.
    if name.starts_with('<')
        || descriptor.ret.ty != CodeType::Object
        || descriptor.params.iter().any(|ty| ty.ty != CodeType::Object)
    {
        return false;
    }
    cx.struct_context
        .bootstrap_class(class)
        .is_some_and(|owner| {
            owner
                .get_method(name, descriptor.as_str())
                .is_some_and(|method| method.has_modifier(ACC_PUBLIC | ACC_VARARGS))
        })
}
