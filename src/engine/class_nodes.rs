// Copyright 2000-2024 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Class identities shared by allocation expressions, nested-class processing
//! and the import collector.

use std::ops::{Index, IndexMut};
use std::sync::Arc;

use arcstr::ArcStr;
use index_vec::{IndexVec, define_index_type};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::decompiler::{
    ir::{ExprId, IrNode},
    vars::var_version_pair::VarVersionPair,
};
use crate::structs::StructClass;
use crate::types::VarType;
use crate::util::interpreter_util::make_unique_key;
use crate::util::jhash::{JHashMap, JHashSet};

mod lambda;
mod load;
mod preparation;

pub(super) use lambda::LambdaScan;
pub use lambda::process_lambdas;
pub use load::load_classes;
pub(super) use preparation::{ClassObservations, ClassSnapshot, NeedsClassSession};

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
    preparing: Option<Box<preparation::WorkerClasses>>,
}

impl ClassNodes {
    /// Copy the tree returned by `load_classes` before publishing any method
    /// graphs or lambda nodes. IDs, aliases and nested-class order stay valid.
    /// Parsed classes are shared; each session owns its mutable node table.
    pub(super) fn initial_copy(&self) -> Self {
        assert!(self.preparing.is_none() && self.wrapper_orders.is_empty());
        Self {
            arena: self.arena.iter().map(ClassNode::initial_copy).collect(),
            names: self.names.clone(),
            ..Self::default()
        }
    }

    pub(super) fn ir_root_scan_bytes(&self) -> u64 {
        self.arena.len() as u64 * size_of::<ClassNode>() as u64
    }

    pub fn id(&self, name: &str) -> Option<ClassNodeId> {
        self.require_class_session();
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

    pub(crate) fn visit_ir_roots(&self, mut visit: impl FnMut(IrNode)) {
        // A synthetic name may have been replaced in the name table while
        // the original node remains accessible through the class tree.
        for node in &self.arena {
            if let Some(invocation) = node.super_invocation {
                visit(invocation.into());
            }
            if let Some(wrapper) = &node.wrapper {
                wrapper.visit_ir_roots(&mut visit);
            }
        }
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
    pub enclosing_classes: JHashSet<ArcStr>,
    pub parent: Option<ClassNodeId>,
    pub nested: Vec<ClassNodeId>,
    pub anonymous_type: Option<VarType>,
    pub lambda: Option<LambdaInformation>,
    /// Published after all declared methods finish processing.
    pub wrapper: Option<super::class_wrapper::ClassWrapper>,
    pub fields_to_vars: JHashMap<String, VarVersionPair>,
    pub super_invocation: Option<ExprId>,
    /// ClassWrapper members consumed by source-level rewrites.
    pub hidden_members: FxHashSet<String>,
}

#[derive(Clone, PartialEq, Eq)]
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
    fn initial_copy(&self) -> Self {
        assert!(
            self.wrapper.is_none()
                && self.super_invocation.is_none()
                && self.lambda.is_none()
                && self.kind != ClassKind::Lambda
                && self.fields_to_vars.is_empty()
                && self.hidden_members.is_empty(),
            "class groups require the initial class tree"
        );
        Self {
            class: Arc::clone(&self.class),
            kind: self.kind,
            access: self.access,
            simple_name: self.simple_name.clone(),
            enclosing_method: self.enclosing_method.clone(),
            enclosing_classes: self.enclosing_classes.clone(),
            parent: self.parent,
            nested: self.nested.clone(),
            anonymous_type: self.anonymous_type.clone(),
            lambda: None,
            wrapper: None,
            fields_to_vars: Default::default(),
            super_invocation: None,
            hidden_members: Default::default(),
        }
    }

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
            enclosing_classes: JHashSet::new(),
            parent: None,
            nested: Vec::new(),
            anonymous_type: None,
            lambda: None,
            wrapper: None,
            fields_to_vars: Default::default(),
            super_invocation: None,
            hidden_members: Default::default(),
        }
    }
}
