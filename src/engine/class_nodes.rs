// Copyright 2000-2024 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Class identities shared by allocation expressions, nested-class processing
//! and the import collector. Keys are the internal names in mapRootClasses.

use std::sync::Arc;

use arcstr::ArcStr;
use rustc_hash::{FxHashMap, FxHashSet};

use crate::structs::StructClass;
use crate::types::VarType;
use crate::util::interpreter_util::make_unique_key;

mod load;

pub use load::load_classes;

pub type ClassNodes = FxHashMap<ArcStr, ClassNode>;

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
    pub parent: Option<ArcStr>,
    pub nested: Vec<ArcStr>,
    pub anonymous_type: Option<VarType>,
    pub method_reference: bool,
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
            method_reference: false,
        }
    }
}
