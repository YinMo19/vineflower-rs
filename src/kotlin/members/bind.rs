// SPDX-License-Identifier: Apache-2.0

use std::{io, sync::Arc};

use arcstr::ArcStr;

use crate::{
    code::code_constants::ACC_STATIC,
    engine::Cx,
    structs::{StructClass, StructField, StructMember, StructMethod},
};

use super::{DefaultArguments, FieldElement, Hidden, MethodElement, state};
use crate::kotlin::declarations::resolve;
use crate::kotlin::metadata::{NameResolver, proto::jvm::JvmMethodSignature};

mod functions;
mod properties;

pub(super) use functions::{constructors, functions};
pub(super) use properties::properties;

fn method(cx: &Cx, class: &StructClass, name: &str, descriptor: &str) -> Option<Arc<StructMethod>> {
    cx.kotlin_members
        .as_ref()
        .and_then(|members| members.find_method(class, name, descriptor))
        .or_else(|| class.get_method(name, descriptor))
        .cloned()
}

fn field(cx: &Cx, class: &StructClass, name: &str, descriptor: &str) -> Option<Arc<StructField>> {
    cx.kotlin_members
        .as_ref()
        .and_then(|members| members.find_field(class, name, descriptor))
        .or_else(|| class.get_field(name, descriptor))
        .cloned()
}

fn resolve_signature(
    names: &NameResolver,
    signature: Option<&JvmMethodSignature>,
) -> io::Result<(ArcStr, ArcStr)> {
    let signature = signature.copied().unwrap_or_default();
    Ok((
        resolve(names, signature.name())?,
        resolve(names, signature.desc())?,
    ))
}

fn hide_method(cx: &mut Cx, method: &Arc<StructMethod>, reason: Hidden) {
    state(cx).methods.get_mut(method).element = Some(MethodElement::Hidden(reason));
}

fn hide_field(cx: &mut Cx, field: &Arc<StructField>, reason: Hidden) {
    state(cx).fields.get_mut(field).element = Some(FieldElement::Hidden(reason));
}

fn hide_equivalent_method(
    cx: &mut Cx,
    class: &StructClass,
    name: &str,
    descriptor: &str,
    reason: Hidden,
) {
    if let Some(method) = method(cx, class, name, descriptor) {
        hide_method(cx, &method, reason);
    }
}

fn default_arguments(
    cx: &mut Cx,
    owner: &StructClass,
    companion_parent: Option<&StructClass>,
    name: ArcStr,
    descriptor: ArcStr,
) -> DefaultArguments {
    hide_equivalent_method(cx, owner, &name, &descriptor, Hidden::DefaultImpl);
    if let Some(parent) = companion_parent {
        hide_equivalent_method(cx, parent, &name, &descriptor, Hidden::DefaultImpl);
    }
    DefaultArguments::Method { name, descriptor }
}
