// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! `ClassesProcessor.loadClasses` builds the class tree before method processing.

use std::collections::{VecDeque, hash_map::Entry};
use std::sync::Arc;

use arcstr::ArcStr;
use rustc_hash::{FxHashMap, FxHashSet};

use super::{ClassKind, ClassNode, ClassNodes};
use crate::code::code_constants::*;
use crate::engine::Options;
use crate::structs::attr::InnerClassEntry;
use crate::structs::{StructClass, StructContext};
use crate::types::VarType;
use crate::util::interpreter_util::make_unique_key;

/// Loads nodes for the eligible own classes. `include` combines the configured
/// include/exclude name filters. The whitelist limits node creation while
/// allowing metadata from eligible classes outside the whitelist.
pub fn load_classes(
    context: &StructContext,
    options: &Options,
    mut include: impl FnMut(&str) -> bool,
    mut whitelist: impl FnMut(&str) -> bool,
    mut rename: impl FnMut(&str, &str) -> Option<ArcStr>,
) -> ClassNodes {
    let mut names = FxHashSet::default();
    let mut nodes = ClassNodes::default();
    let mut nesting = Nesting::default();

    for class in context.get_own_classes() {
        let name = &class.qualified_name;
        if !names.insert(name.clone()) {
            log::error!("Skipping processing already existing class: {name}");
            continue;
        }
        if !include(name) {
            continue;
        }
        if options.decompile_inner
            && let Some(attr) = &class.attributes.inner_classes
        {
            for entry in &attr.entries {
                nesting.record(context, options, name, entry, &mut rename);
            }
        }
        if whitelist(name) {
            nodes.insert(name.clone(), ClassNode::root(class));
        }
    }

    if options.decompile_inner {
        nesting.attach(&mut nodes, options.verify_anonymous_classes);
    }
    nodes
}

#[derive(Debug)]
struct Inner {
    simple_name: Option<ArcStr>,
    kind: ClassKind,
    access: i32,
    source: ArcStr,
    enclosing_name: Option<ArcStr>,
}

impl Inner {
    fn matches(&self, other: &Inner) -> bool {
        self.kind == other.kind
            && self.access == other.access
            && self.simple_name == other.simple_name
            && self.enclosing_name == other.enclosing_name
    }

    fn priority(&self, inner: &str, enclosing: &str) -> u8 {
        if self.source.as_str() == inner {
            1
        } else if self.source.as_str() == enclosing {
            2
        } else {
            3
        }
    }
}

#[derive(Default)]
struct Nesting {
    inner: FxHashMap<ArcStr, Inner>,
    nested_refs: FxHashMap<ArcStr, FxHashSet<ArcStr>>,
    enclosing_refs: FxHashMap<ArcStr, FxHashSet<ArcStr>>,
    renamed_simple_names: FxHashMap<ArcStr, ArcStr>,
}

impl Nesting {
    fn record(
        &mut self,
        context: &StructContext,
        options: &Options,
        source: &ArcStr,
        entry: &InnerClassEntry,
        rename: &mut impl FnMut(&str, &str) -> Option<ArcStr>,
    ) {
        let inner_name = &entry.inner_name;
        let simple_name = self
            .renamed_simple_names
            .get(inner_name)
            .cloned()
            .or_else(|| {
                let old = entry.simple_name.as_ref()?;
                let Some(new) = rename(inner_name, old) else {
                    return Some(old.clone());
                };
                self.renamed_simple_names
                    .insert(inner_name.clone(), new.clone());
                Some(new)
            });

        let inner = if entry.enclosing_name.is_none() || entry.simple_name.is_some() {
            context.get_class(inner_name)
        } else {
            None
        };
        let enclosing_method = inner
            .as_ref()
            .and_then(|inner| inner.attributes.enclosing_method.as_ref());
        let kind = if entry.simple_name.is_none() {
            ClassKind::Anonymous
        } else if enclosing_method.is_some_and(|attr| attr.method_name.is_some()) {
            ClassKind::Local
        } else {
            ClassKind::Member
        };
        let enclosing_name = entry
            .enclosing_name
            .clone()
            .or_else(|| enclosing_method.map(|attr| attr.class_name.clone()));
        let record = Inner {
            simple_name,
            kind,
            access: entry.access_flags,
            source: source.clone(),
            enclosing_name,
        };

        let reference_owner = if entry.outer_name_idx != 0 {
            let Some(owner) = &entry.enclosing_name else {
                return;
            };
            owner
        } else {
            source
        };
        if reference_owner == inner_name {
            return;
        }
        if options.validate_inner_classes_names && kind == ClassKind::Member {
            let original_simple_name = entry.simple_name.as_deref().unwrap();
            if inner_name.as_str() != format!("{reference_owner}${original_simple_name}") {
                return;
            }
        }
        if !context
            .get_class(reference_owner)
            .is_some_and(|class| class.own)
        {
            return;
        }

        match self.inner.entry(inner_name.clone()) {
            Entry::Vacant(slot) => {
                slot.insert(record);
            }
            Entry::Occupied(mut slot) if !slot.get().matches(&record) => {
                let old = slot.get();
                let replace = record.priority(inner_name, reference_owner)
                    < old.priority(inner_name, reference_owner);
                if options.warn_inconsistent_inner_attributes {
                    log::warn!("Inconsistent inner class entries for {inner_name}!");
                    log::warn!("  {}: {old:?}", old.source);
                    log::warn!("  {}: {record:?}", record.source);
                    if replace {
                        log::warn!("Changing mapping to {inner_name} -> {record:?}");
                    }
                }
                if replace {
                    slot.insert(record);
                }
            }
            Entry::Occupied(_) => {}
        }

        self.nested_refs
            .entry(reference_owner.clone())
            .or_default()
            .insert(inner_name.clone());
        self.enclosing_refs
            .entry(inner_name.clone())
            .or_default()
            .insert(reference_owner.clone());
    }

    fn attach(&self, nodes: &mut ClassNodes, verify_anonymous: bool) {
        let roots: Vec<_> = nodes
            .names
            .iter()
            .filter(|(name, _)| !self.inner.contains_key(*name))
            .map(|(_, &id)| id)
            .collect();

        for root in roots {
            let mut visited = FxHashSet::default();
            visited.insert(nodes[root].class.qualified_name.clone());
            let mut pending = VecDeque::from([root]);
            while let Some(owner) = pending.pop_front() {
                let enclosing = Arc::clone(&nodes[owner].class);
                let name = &enclosing.qualified_name;
                let Some(references) = self.nested_refs.get(name) else {
                    continue;
                };
                let Some(inner) = enclosing
                    .attributes
                    .inner_classes
                    .as_ref()
                    .filter(|attr| !attr.entries.is_empty())
                else {
                    log::warn!("{name} does not contain inner classes!");
                    continue;
                };

                for entry in &inner.entries {
                    let child = &entry.inner_name;
                    if !references.contains(child) {
                        continue;
                    }
                    let record = &self.inner[child];
                    if record.enclosing_name.as_ref() != Some(name)
                        || !visited.insert(child.clone())
                    {
                        continue;
                    }
                    let Some(child_id) = nodes.id(child) else {
                        log::warn!("Nested class {child} missing!");
                        continue;
                    };
                    let node = &mut nodes[child_id];
                    Self::attach_child(node, record, &enclosing, verify_anonymous);
                    node.parent = Some(owner);
                    node.enclosing_classes
                        .extend(self.enclosing_refs[child].iter().cloned());
                    nodes[owner].nested.push(child_id);
                    pending.push_back(child_id);
                }
                nodes.sort_nested(owner);
            }
        }
    }

    fn attach_child(
        node: &mut ClassNode,
        record: &Inner,
        enclosing: &StructClass,
        verify_anonymous: bool,
    ) {
        node.simple_name.clone_from(&record.simple_name);
        node.kind = record.kind;
        node.access = record.access;
        if node.kind == ClassKind::Anonymous {
            // Anonymous classes inside lambdas report the lambda's enclosing method.
            node.enclosing_method = None;
            if verify_anonymous && !is_anonymous(&node.class, enclosing) {
                node.kind = ClassKind::Local;
            }
        }

        if node.kind == ClassKind::Anonymous {
            node.access &= !ACC_STATIC;
            let class = &node.class;
            let anonymous_type = class.interface_names.first().or_else(|| {
                class
                    .super_class
                    .as_ref()
                    .map(|super_class| super_class.get_string())
            });
            node.anonymous_type = anonymous_type.map(|name| VarType::from_signature_cl(name, true));
        } else if node.kind == ClassKind::Local {
            let mut allowed = ACC_ABSTRACT | ACC_FINAL;
            if enclosing.version.has_local_enums_and_interfaces() {
                allowed |= ACC_INTERFACE | ACC_ENUM;
                if node.access & ACC_ENUM != 0 {
                    allowed |= ACC_STATIC;
                }
            }
            node.access &= allowed;
        }
    }
}

fn is_anonymous(class: &StructClass, enclosing: &StructClass) -> bool {
    let name = &class.qualified_name;
    if !class.interfaces.is_empty() {
        let has_nontrivial_super = class.super_class.as_ref().is_some_and(|super_class| {
            VarType::from_signature_cl(super_class.get_string(), true) != VarType::VARTYPE_OBJECT
        });
        if has_nontrivial_super || class.interfaces.len() > 1 {
            log::warn!(
                "Inconsistent anonymous class definition: '{name}'. Multiple interfaces and/or super class defined."
            );
            return false;
        }
    } else if class.super_class.is_none() {
        log::warn!(
            "Inconsistent anonymous class definition: '{name}'. Neither interface nor super class defined."
        );
        return false;
    }

    let enclosing_method = class
        .attributes
        .enclosing_method
        .as_ref()
        .and_then(|attr| attr.method_name.as_ref());
    let mut references = 0;
    for method in &enclosing.methods {
        if enclosing_method.is_some_and(|name| *name != method.name) {
            continue;
        }
        let seq = match method.expand_data(enclosing) {
            Ok(Some(seq)) => seq,
            Ok(None) => continue,
            Err(error) => {
                let key = make_unique_key(&method.name, &method.descriptor);
                log::warn!(
                    "Could not read method while checking anonymous class definition: '{}', '{key}': {error}",
                    enclosing.qualified_name
                );
                return false;
            }
        };

        for instruction in seq.instructions {
            let opcode = instruction.opcode;
            let is_reference = match opcode {
                OPC_CHECKCAST | OPC_INSTANCEOF | OPC_NEW | OPC_ANEWARRAY | OPC_MULTIANEWARRAY => {
                    enclosing
                        .pool
                        .get_primitive_constant(instruction.operand(0))
                        .is_some_and(|constant| constant.get_string() == name)
                }
                OPC_GETSTATIC | OPC_PUTSTATIC => enclosing
                    .pool
                    .get_link_constant(instruction.operand(0))
                    .is_some_and(|constant| constant.classname.as_ref() == Some(name)),
                _ => false,
            };
            if is_reference {
                references += 1;
                if references > 1 || !matches!(opcode, OPC_NEW | OPC_ANEWARRAY | OPC_MULTIANEWARRAY)
                {
                    log::warn!(
                        "Inconsistent references to the class '{name}' which is supposed to be anonymous"
                    );
                    return false;
                }
            }
        }
    }
    true
}
