// Copyright 2000-2024 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Class identities shared by allocation expressions, nested-class processing
//! and the import collector.

use std::ops::{Index, IndexMut};
use std::sync::Arc;

use arcstr::ArcStr;
use index_vec::{IndexVec, define_index_type};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::structs::StructClass;
use crate::types::VarType;
use crate::util::interpreter_util::make_unique_key;

mod lambda;
mod load;

pub use lambda::process_lambdas;
pub use load::load_classes;

define_index_type! {
    pub struct ClassNodeId = u32;
}

/// The class tree retains every node by identity. The name table points to the
/// latest node registered under each internal or synthetic name.
#[derive(Default)]
pub struct ClassNodes {
    arena: IndexVec<ClassNodeId, ClassNode>,
    names: FxHashMap<ArcStr, ClassNodeId>,
    wrapper_orders: FxHashMap<ClassNodeId, Vec<ClassNodeId>>,
}

impl ClassNodes {
    pub fn id(&self, name: &str) -> Option<ClassNodeId> {
        self.names.get(name).copied()
    }

    pub fn get(&self, name: &str) -> Option<&ClassNode> {
        self.id(name).map(|id| &self[id])
    }

    pub fn insert(&mut self, name: ArcStr, node: ClassNode) -> ClassNodeId {
        let id = self.arena.push(node);
        self.names.insert(name, id);
        id
    }

    pub fn iter(&self) -> impl Iterator<Item = (&ArcStr, &ClassNode)> {
        self.names.iter().map(|(name, &id)| (name, &self[id]))
    }

    /// Non-lambda wrappers in the order they finish initialization for a root.
    pub fn wrapper_order(&self, root: ClassNodeId) -> &[ClassNodeId] {
        self.wrapper_orders.get(&root).map_or(&[], Vec::as_slice)
    }

    pub(super) fn set_wrapper_order(&mut self, root: ClassNodeId, order: Vec<ClassNodeId>) {
        self.wrapper_orders.insert(root, order);
    }

    /// Lambda nodes share the class wrapper of their nearest non-lambda owner.
    pub(crate) fn wrapper_owner(&self, mut node: ClassNodeId) -> Option<ClassNodeId> {
        while self[node].kind == ClassKind::Lambda {
            node = self[node].parent?;
        }
        Some(node)
    }

    pub fn sort_nested(&mut self, owner: ClassNodeId) {
        let mut children = std::mem::take(&mut self[owner].nested);
        // ClassNode.compareTo uses classStruct.qualifiedName, so lambda nodes
        // from the same class compare equal and keep their allocation order.
        children.sort_by(|&left, &right| {
            self[left]
                .class
                .qualified_name
                .encode_utf16()
                .cmp(self[right].class.qualified_name.encode_utf16())
        });
        self[owner].nested = children;
    }
}

impl Index<ClassNodeId> for ClassNodes {
    type Output = ClassNode;

    fn index(&self, id: ClassNodeId) -> &ClassNode {
        &self.arena[id]
    }
}

impl IndexMut<ClassNodeId> for ClassNodes {
    fn index_mut(&mut self, id: ClassNodeId) -> &mut ClassNode {
        &mut self.arena[id]
    }
}

impl Index<&str> for ClassNodes {
    type Output = ClassNode;

    fn index(&self, name: &str) -> &ClassNode {
        &self[self.names[name]]
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ClassKind {
    Root,
    Member,
    Anonymous,
    Local,
    Lambda,
}

pub struct ClassNode {
    pub class: Arc<StructClass>,
    pub kind: ClassKind,
    pub access: i32,
    pub simple_name: Option<ArcStr>,
    pub enclosing_method: Option<ArcStr>,
    pub enclosing_classes: FxHashSet<ArcStr>,
    pub parent: Option<ClassNodeId>,
    pub nested: Vec<ClassNodeId>,
    pub anonymous_type: Option<VarType>,
    pub lambda: Option<LambdaInformation>,
    /// Published after all declared methods finish processing.
    pub wrapper: Option<super::class_wrapper::ClassWrapper>,
    /// ClassWrapper members consumed by source-level rewrites.
    pub hidden_members: FxHashSet<String>,
}

pub struct LambdaInformation {
    pub method_name: ArcStr,
    pub method_descriptor: ArcStr,
    pub content_class_name: ArcStr,
    pub content_method_name: ArcStr,
    pub content_method_descriptor: ArcStr,
    pub content_method_invocation_type: i32,
    pub content_method_key: ArcStr,
    pub is_method_reference: bool,
    pub is_content_method_static: bool,
}

impl ClassNode {
    pub fn root(class: Arc<StructClass>) -> Self {
        let simple_name = class.qualified_name.rsplit('/').next().unwrap().into();
        let enclosing_method = class.attributes.enclosing_method.as_ref().and_then(|attr| {
            Some(
                make_unique_key(
                    attr.method_name.as_deref()?,
                    attr.method_descriptor.as_deref()?,
                )
                .into(),
            )
        });
        Self {
            access: class.access_flags,
            class,
            kind: ClassKind::Root,
            simple_name: Some(simple_name),
            enclosing_method,
            enclosing_classes: FxHashSet::default(),
            parent: None,
            nested: Vec::new(),
            anonymous_type: None,
            lambda: None,
            wrapper: None,
            hidden_members: Default::default(),
        }
    }
}
