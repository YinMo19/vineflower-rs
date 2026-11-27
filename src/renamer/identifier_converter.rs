//! IdentifierConverter's inference of the names shared by inherited members.

use std::collections::VecDeque;
use std::io;
use std::sync::Arc;

use arcstr::ArcStr;
use indexmap::IndexMap;
use rustc_hash::{FxHashMap, FxHashSet};

use super::converter_helper::{replace_simple_class_name, simple_class_name};
use super::pool_interceptor::PoolInterceptor;
use super::{IdentifierKind, IdentifierRenamer};
use crate::code::code_constants::{ACC_INTERFACE, ACC_NATIVE, ACC_PRIVATE};
use crate::structs::{StructClass, StructContext, StructMember};
use crate::types::{FieldDescriptor, MethodDescriptor, NewClassNameBuilder};

type MethodNames = IndexMap<String, String>;
type InheritedNames = IndexMap<ArcStr, MethodNames>;

/// Re-read the context's sources under an interceptor that assigns the Java
/// identifiers. Use the same helper again when constructing ClassNodes.
pub fn rename(context: &mut StructContext, helper: &mut dyn IdentifierRenamer) -> io::Result<()> {
    let inheritance = Inheritance::build(context);
    let interfaces = inheritance.reverse_postorder(&inheritance.interface_roots);
    let classes = inheritance.reverse_postorder(&inheritance.class_roots);
    let mut converter = Converter {
        context,
        helper,
        interceptor: PoolInterceptor::default(),
    };
    for &id in interfaces.iter().chain(&classes) {
        converter.rename_class(&inheritance.nodes[id].class);
    }
    let mut interface_names = InheritedNames::new();
    for id in interfaces {
        let class = &inheritance.nodes[id].class;
        let mut names = MethodNames::new();
        for interface in &class.interface_names {
            if let Some(inherited) = interface_names.get(interface) {
                inherit(&mut names, inherited);
            }
        }
        converter.rename_members(class, &mut names);
        interface_names.insert(class.qualified_name.clone(), names);
    }
    let mut class_names = InheritedNames::new();
    for id in classes {
        let node = &inheritance.nodes[id];
        let class = &node.class;
        let mut names = MethodNames::new();
        if let Some(super_class) = &class.super_class
            && let Some(inherited) = class_names.get(super_class.get_string())
        {
            inherit(&mut names, inherited);
        }
        converter.inherit_interfaces(class, &interface_names, &mut names);
        converter.rename_members(class, &mut names);
        if !node.subclasses.is_empty() {
            class_names.insert(class.qualified_name.clone(), names);
        }
    }
    context.try_reload_context(Some(Arc::new(converter.interceptor)))
}

struct Converter<'a> {
    context: &'a StructContext,
    helper: &'a mut dyn IdentifierRenamer,
    interceptor: PoolInterceptor,
}

impl Converter<'_> {
    fn rename_class(&mut self, class: &StructClass) {
        if !class.own {
            return;
        }
        let name = &class.qualified_name;
        let simple = simple_class_name(name);
        if !self
            .helper
            .to_be_renamed(IdentifierKind::Class, simple, None, None)
        {
            return;
        }
        loop {
            let replacement = self.helper.next_class_name(name, Some(simple));
            let qualified = replace_simple_class_name(name, &replacement);
            if !self.context.has_class(&qualified) {
                self.interceptor.add_name(name, &qualified);
                return;
            }
        }
    }

    fn inherit_interfaces(
        &mut self,
        class: &StructClass,
        interfaces: &InheritedNames,
        names: &mut MethodNames,
    ) {
        for interface in &class.interface_names {
            if let Some(inherited) = interfaces.get(interface) {
                inherit(names, inherited);
            } else if let Some(interface) = self.context.get_class(interface) {
                let mut inherited = MethodNames::new();
                self.inherit_interfaces(&interface, interfaces, &mut inherited);
                self.rename_members(&interface, &mut inherited);
                inherit(names, &inherited);
            }
        }
    }

    fn rename_members(&mut self, class: &StructClass, inherited: &mut MethodNames) {
        let owner = &class.qualified_name;
        let new_owner = self.interceptor.get_name(owner).unwrap_or(owner).to_owned();
        let declared: FxHashSet<_> = class
            .methods
            .iter()
            .map(|method| method.name.as_str())
            .collect();
        for (method, key) in class.methods.iter().zip(class.methods.lst_keys()) {
            let key = key.as_ref().expect("Method has no signature key");
            let private = method.has_modifier(ACC_PRIVATE);
            let name = method.name.as_str();
            let descriptor = method.descriptor.as_str();
            if !class.own || method.has_modifier(ACC_NATIVE) {
                if !private {
                    inherited.insert(key.clone(), name.to_owned());
                }
            } else if self.helper.to_be_renamed(
                IdentifierKind::Method,
                owner,
                Some(name),
                Some(descriptor),
            ) {
                let renamed = if let Some(inherited_name) = inherited.get(key).filter(|_| !private)
                {
                    inherited_name.clone()
                } else {
                    let mut candidate = self.helper.next_method_name(owner, name, descriptor);
                    while declared.contains(candidate.as_str()) {
                        candidate = self.helper.next_method_name(owner, &candidate, descriptor);
                    }
                    if !private {
                        inherited.insert(key.clone(), candidate.clone());
                    }
                    candidate
                };
                let mapped = MethodDescriptor::parse_descriptor(descriptor)
                    .build_new_descriptor(&self.interceptor);
                self.interceptor.add_name(
                    &format!("{owner} {name} {descriptor}"),
                    &format!(
                        "{new_owner} {renamed} {}",
                        mapped.as_deref().unwrap_or(descriptor)
                    ),
                );
            }
        }
        if !class.own {
            return;
        }
        let declared: FxHashSet<_> = class
            .fields
            .iter()
            .map(|field| field.name.as_str())
            .collect();
        for field in &class.fields {
            let name = field.name.as_str();
            let descriptor = field.descriptor.as_str();
            if self
                .helper
                .to_be_renamed(IdentifierKind::Field, owner, Some(name), Some(descriptor))
            {
                let mut renamed = self.helper.next_field_name(owner, name, descriptor);
                while declared.contains(renamed.as_str()) {
                    renamed = self.helper.next_field_name(owner, name, descriptor);
                }
                let mapped = FieldDescriptor::parse_descriptor(descriptor)
                    .build_new_descriptor(&self.interceptor);
                self.interceptor.add_name(
                    &format!("{owner} {name} {descriptor}"),
                    &format!(
                        "{new_owner} {renamed} {}",
                        mapped.as_deref().unwrap_or(descriptor)
                    ),
                );
            }
        }
    }
}

fn inherit(names: &mut MethodNames, parent: &MethodNames) {
    names.extend(parent.iter().map(|(key, name)| (key.clone(), name.clone())));
}

impl NewClassNameBuilder for PoolInterceptor {
    fn build_new_classname(&self, class_name: &str) -> Option<String> {
        self.get_name(class_name).map(str::to_owned)
    }
}

#[derive(Default)]
struct Inheritance {
    nodes: Vec<HierarchyNode>,
    class_roots: Vec<usize>,
    interface_roots: Vec<usize>,
}

struct HierarchyNode {
    class: Arc<StructClass>,
    subclasses: Vec<usize>,
}

impl Inheritance {
    fn build(context: &StructContext) -> Self {
        let mut tree = Self::default();
        let mut identities: FxHashMap<ArcStr, usize> = FxHashMap::default();
        for class in context.get_own_classes() {
            let mut pending: VecDeque<(Arc<StructClass>, Option<usize>)> =
                VecDeque::from([(class, None)]);
            while let Some((class, child)) = pending.pop_front() {
                if let Some(&id) = identities.get(&class.qualified_name) {
                    if let Some(child) = child {
                        tree.nodes[id].subclasses.push(child);
                    }
                    // The Java walk stops the pending path on its first known parent.
                    break;
                }
                let id = tree.nodes.len();
                identities.insert(class.qualified_name.clone(), id);
                let interface = class.has_modifier(ACC_INTERFACE);
                let parents = if interface {
                    class.interface_names.as_slice()
                } else {
                    class
                        .super_class
                        .as_ref()
                        .map(|parent| std::slice::from_ref(parent.get_string()))
                        .unwrap_or(&[])
                };
                let before = pending.len();
                pending.extend(
                    parents
                        .iter()
                        .filter_map(|name| context.get_class(name))
                        .map(|parent| (parent, Some(id))),
                );
                if pending.len() == before {
                    if interface {
                        tree.interface_roots.push(id);
                    } else {
                        tree.class_roots.push(id);
                    }
                }
                tree.nodes.push(HierarchyNode {
                    class,
                    subclasses: child.into_iter().collect(),
                });
            }
        }
        tree
    }

    fn reverse_postorder(&self, roots: &[usize]) -> Vec<usize> {
        let mut stack: Vec<_> = roots.iter().map(|&root| (root, 0)).collect();
        let mut seen = FxHashSet::default();
        let mut order = Vec::new();
        while let Some((node, next)) = stack.last_mut() {
            seen.insert(*node);
            let child = self.nodes[*node].subclasses[*next..]
                .iter()
                .position(|child| !seen.contains(child));
            if let Some(child) = child {
                *next += child + 1;
                let child = self.nodes[*node].subclasses[*next - 1];
                stack.push((child, 0));
            } else {
                let (node, _) = stack.pop().unwrap();
                order.push(node);
            }
        }
        order.reverse();
        order
    }
}
