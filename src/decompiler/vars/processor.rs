// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! State tied to a method for the lifetime of its wrapper. Recomputing SSA
//! replaces the version and type tables while keeping the naming state.

use std::sync::Arc;

use arcstr::ArcStr;
use rustc_hash::{FxHashMap, FxHashSet};

use super::{var_version_pair::VarVersionPair, versions::VarVersions};
use crate::code::code_constants::ACC_STATIC;
use crate::structs::attr::LocalVariable;
use crate::structs::{StructClass, StructMember, StructMethod};
use crate::types::MethodDescriptor;
use crate::util::jhash::JHashMap;

#[derive(Default)]
pub struct VarProcessor {
    pub versions: VarVersions,
    pub names: JHashMap<VarVersionPair, Option<ArcStr>>,
    pub this_vars: JHashMap<VarVersionPair, ArcStr>,
    pub name_collector: VarNamesCollector,
    pub params: Vec<VarVersionPair>,
    pub clashing_names: FxHashMap<VarVersionPair, ArcStr>,
    pub local_variables: FxHashMap<VarVersionPair, Arc<LocalVariable>>,
}

impl VarProcessor {
    pub(crate) fn name_declared_parameters(&mut self, class: &StructClass, method: &StructMethod) {
        let is_static = method.has_modifier(ACC_STATIC);
        let descriptor = MethodDescriptor::parse_descriptor(&method.descriptor);
        if !is_static {
            self.this_vars
                .insert(VarVersionPair::new(0, 0), class.qualified_name.clone());
        }
        for slot in (!is_static)
            .then_some(0)
            .into_iter()
            .chain(descriptor.parameter_slots(is_static).map(|(slot, _)| slot))
        {
            let pair = VarVersionPair::new(slot, 0);
            self.names
                .insert(pair, Some(self.name_collector.free_index(slot)));
            self.params.push(pair);
        }
    }

    pub(crate) fn refresh_names(&mut self, collector: &mut VarNamesCollector) {
        for (pair, name) in JHashMap::copy_of(&self.names).iter() {
            self.names
                .insert(*pair, collector.free_name(name.as_deref()));
        }
    }
}

#[derive(Default)]
pub struct VarNamesCollector {
    used: FxHashSet<Option<ArcStr>>,
}

impl VarNamesCollector {
    pub fn add_name(&mut self, name: &str) {
        self.used.insert(Some(name.into()));
    }

    pub fn free_index(&mut self, index: i32) -> ArcStr {
        self.free_name(Some(&format!("var{index}"))).unwrap()
    }

    /// MethodParameters permits a null name. Java reserves that name too,
    /// and its first collision produces the string "nullx".
    pub fn free_name(&mut self, proposed: Option<&str>) -> Option<ArcStr> {
        let mut name = proposed.map(ArcStr::from);
        while !self.used.insert(name.clone()) {
            name = Some(format!("{}x", name.as_deref().unwrap_or("null")).into());
        }
        name
    }
}
