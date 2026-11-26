// SPDX-License-Identifier: Apache-2.0

//! Canonical record constructor preparation before writing the class body.

use std::{borrow::Cow, sync::Arc};

use crate::code::code_constants::INIT_NAME;
use crate::decompiler::exps::{Expr, ExprKind, Variable};
use crate::decompiler::ir::{ExprId, Ir};
use crate::decompiler::vars::var_version_pair::VarVersionPair;
use crate::engine::Cx;
use crate::engine::class_wrapper::MethodSlot;
use crate::structs::{StructClass, StructMethod, StructRecordComponent};
use crate::types::MethodDescriptor;

pub(super) fn canonical_constructor<'a>(
    class: &'a StructClass,
    components: &[StructRecordComponent],
) -> Option<&'a Arc<StructMethod>> {
    let mut desc = String::from("(");
    for field in components {
        desc.push_str(&field.descriptor);
    }
    desc.push_str(")V");
    class.get_method(INIT_NAME, &desc)
}

/// `RecordHelper.fixupCanonicalConstructor`.
pub(super) fn fixup_canonical_constructor(cx: &mut Cx, method: MethodSlot) {
    let class = Arc::clone(&cx.class_nodes[method.node].class);
    let Some(components) = class.get_record_components() else {
        return;
    };
    let Some(canonical) = canonical_constructor(&class, components) else {
        return;
    };
    let wrapper = method.get(cx);
    if !Arc::ptr_eq(canonical, &wrapper.method) {
        return;
    }
    let descriptor = MethodDescriptor::parse_descriptor(&wrapper.method.descriptor);
    if descriptor.params.len() != components.len() {
        return;
    }
    let variables = wrapper.variables;
    let has_body = wrapper.root().is_some();
    for (component, (index, _)) in components.iter().zip(descriptor.parameter_slots(false)) {
        cx.ir[variables]
            .clashing_names
            .insert(VarVersionPair::new(index, 0), component.name.clone());
    }

    if !has_body {
        return;
    }
    let lists = cx.wrapper_expr_lists(method);
    // The upstream visitor overwrites the flag for every expression. Only
    // the final expression in regular breadth-first order determines compactness.
    let final_expr = lists
        .iter()
        .rev()
        .find_map(|&list| cx.ir[list].last().copied());
    if !final_expr.is_some_and(|expr| is_component_assignment(cx, expr)) {
        return;
    }
    for list in lists {
        let mut index = 0;
        while index < cx.ir[list].len() {
            if field_assignment(&cx.ir, cx.ir[list][index]).is_some() {
                cx.ir[list].remove(index);
            } else {
                index += 1;
            }
        }
    }
    method.get_mut(cx).is_compact_record_constructor = true;
}

fn field_assignment(ir: &Ir, expr: ExprId) -> Option<(&str, ExprId)> {
    if let ExprKind::Assignment { left, right, .. } = ir[expr].kind
        && let ExprKind::Field(field) = &ir[left].kind
    {
        Some((&field.name, right))
    } else {
        None
    }
}

fn is_component_assignment(cx: &Cx, expr: ExprId) -> bool {
    if let Some((field, value)) = field_assignment(&cx.ir, expr)
        && let Some(var) = Expr::variable(&cx.ir, value)
        && var.lvt.is_some()
    {
        variable_name(cx, var) == field
    } else {
        false
    }
}

/// `VarExprent.getName`: the writing name after scope, LVT and naming-provider changes.
pub(super) fn variable_name<'a>(cx: &'a Cx, var: &'a Variable) -> Cow<'a, str> {
    let pair = var.pair();
    let processor = var.processor.map(|id| &cx.ir[id]);
    let clash = processor.and_then(|p| p.clashing_names.get(&pair));
    let debug = var
        .lvt
        .as_ref()
        .filter(|_| cx.options.use_lvt_names)
        .map(|lvt| lvt.get_name());
    let chosen = clash
        .or(debug)
        .or_else(|| processor.and_then(|p| p.names.get(&pair).and_then(Option::as_ref)));
    if let Some(name) = chosen {
        Cow::Borrowed(name)
    } else if pair.version == 0 {
        Cow::Owned(format!("var{}", pair.var))
    } else {
        Cow::Owned(format!("var{}_{}", pair.var, pair.version))
    }
}
