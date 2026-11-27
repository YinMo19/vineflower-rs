//! Java NestedClassProcessor, operating on the class tree after wrapper publication.

mod captures;
mod declaration;
mod lambda;
mod locals;
mod member_access;

pub(super) use member_access::propagate_member_access;

use lambda::set_lambda_vars;
use locals::insert_local_vars;

use super::{
    Cx,
    class_nodes::{ClassKind, ClassNodeId, ClassNodes},
};
use crate::{
    code::code_constants::ACC_SYNTHETIC, structs::StructMember,
    util::interpreter_util::make_unique_key,
};
use rustc_hash::FxHashSet;
use std::{collections::VecDeque, io};

/// Restore captured variables and local declarations after all wrappers of the
/// compilation unit have been published.
pub fn process_class(cx: &mut Cx, root: ClassNodeId) -> io::Result<()> {
    visit(cx, root, root)
}

fn visit(cx: &mut Cx, root: ClassNodeId, node: ClassNodeId) -> io::Result<()> {
    prepare_nested_node(cx, root, node)?;
    for i in 0..cx.class_nodes[node].nested.len() {
        let child = cx.class_nodes[node].nested[i];
        let nested = &cx.class_nodes[child];
        if nested.kind == ClassKind::Lambda {
            set_lambda_vars(cx, node, child)?;
        } else if nested.kind != ClassKind::Member
            || nested.access & crate::code::code_constants::ACC_STATIC == 0
        {
            insert_local_vars(cx, node, child)?;
            let nested = &cx.class_nodes[child];
            if nested.kind == ClassKind::Local
                && let Some(enclosing) = nested.enclosing_method.as_deref()
                && let Some(method) = super::class_wrapper::MethodSlot::by_key(cx, node, enclosing)
            {
                declaration::set_local_class_definition(cx, method, child);
            }
        }
    }
    cx.class_nodes[node]
        .nested
        .clone()
        .into_iter()
        .try_for_each(|child| visit(cx, root, child))
}

/// Start a NestedClassProcessor visit. The owner must finish applying its
/// captures and inserting local definitions before children are visited.
fn prepare_nested_node(cx: &mut Cx, root: ClassNodeId, node: ClassNodeId) -> io::Result<()> {
    let classes = &mut cx.class_nodes;
    if let Some(lambda) = &classes[node].lambda
        && !lambda.is_method_reference
        && let Some(content) = classes.id(&classes[node].class.qualified_name)
        && classes[content].wrapper.is_some()
    {
        let key = lambda.content_method_key.to_string();
        classes[content].hidden_members.insert(key);
    }
    if classes[node].nested.is_empty() {
        return Ok(());
    }

    let mut indirect = FxHashSet::default();
    let mut pending: Vec<_> = classes[node]
        .nested
        .iter()
        .flat_map(|&child| classes[child].nested.iter().copied())
        .collect();
    while let Some(child) = pending.pop() {
        if indirect.insert(child) {
            pending.extend(&classes[child].nested);
        }
    }
    classes[node]
        .nested
        .retain(|child| !indirect.contains(child));

    if classes[node].kind != ClassKind::Lambda {
        captures::compute(cx, node)?;
        resolve_enclosing_methods(&mut cx.class_nodes, root, node);
    }
    let classes = &mut cx.class_nodes;
    let (mut nameless, mut synthetics) = (0, 0);
    for i in 0..classes[node].nested.len() {
        let id = classes[node].nested[i];
        let child = &mut classes[id];
        if matches!(child.kind, ClassKind::Member | ClassKind::Local) && child.simple_name.is_none()
        {
            let name = if child.access & ACC_SYNTHETIC != 0 || child.class.is_synthetic() {
                synthetics += 1;
                format!("SyntheticClass_{synthetics}")
            } else {
                log::warn!(
                    "Nameless local or member class {}!",
                    child.class.qualified_name
                );
                nameless += 1;
                format!("NamelessClass_{nameless}")
            };
            child.simple_name = Some(name.into());
        }
    }
    Ok(())
}

fn resolve_enclosing_methods(classes: &mut ClassNodes, root: ClassNodeId, owner: ClassNodeId) {
    for child in classes[owner].nested.clone() {
        let nested = &classes[child];
        if nested.class.is_synthetic()
            || !matches!(nested.kind, ClassKind::Local | ClassKind::Anonymous)
            || nested.enclosing_method.is_some()
        {
            continue;
        }
        let parent = &classes[owner].class;
        if !nested.enclosing_classes.is_empty()
            && let Some(attr) = &nested.class.attributes.enclosing_method
            && let (Some(name), Some(descriptor)) = (&attr.method_name, &attr.method_descriptor)
            && parent.qualified_name == attr.class_name
            && parent.get_method(name, descriptor).is_some()
        {
            classes[child].enclosing_method = Some(make_unique_key(name, descriptor).into());
            continue;
        }
        let old = parent.qualified_name.clone();
        classes[owner].nested.retain(|&id| id != child);
        classes[child].parent = None;
        classes[child].enclosing_classes.remove(&old);
        if !classes[child].enclosing_classes.is_empty() && reattach(classes, root, child) {
            continue;
        }
        let kind = if classes[child].kind == ClassKind::Local {
            "local"
        } else {
            "anonymous"
        };
        log::warn!(
            "Unreferenced {kind} class {}!",
            classes[child].class.qualified_name
        );
    }
}

fn reattach(classes: &mut ClassNodes, root: ClassNodeId, child: ClassNodeId) -> bool {
    let mut pending = VecDeque::from([root]);
    while let Some(parent) = pending.pop_front() {
        if classes[child]
            .enclosing_classes
            .contains(&classes[parent].class.qualified_name)
        {
            classes[parent].nested.push(child);
            classes[child].parent = Some(parent);
            classes.sort_nested(parent);
            return true;
        }
        pending.extend(classes[parent].nested.iter().copied());
    }
    false
}
