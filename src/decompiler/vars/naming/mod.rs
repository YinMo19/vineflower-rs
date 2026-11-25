// Copyright 2000-2024 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Per-method naming providers, selected by the bundled variable-renaming plugin.

mod jad;
mod tiny;

use super::var_version_pair::VarVersionPair;
use crate::code::code_constants::ACC_STATIC;
use crate::engine::Options;
use crate::structs::{StructMember, StructMethod};
use crate::types::{MethodDescriptor, VarType};
use arcstr::ArcStr;
use itertools::Itertools;
use rustc_hash::FxHashMap;

#[derive(Clone)]
pub(crate) enum Names {
    Identity,
    Jad(jad::Jad),
    Tiny(tiny::Tiny),
}

pub(crate) struct VariableNamer {
    names: Names,
    parameters: FxHashMap<i32, ArcStr>,
    rename_parameters: bool,
}

impl VariableNamer {
    pub(crate) fn new(options: &Options) -> Self {
        let kind = options
            .variable_renaming
            .as_deref()
            .or_else(|| options.jad_style_variable_naming.then_some("jad"));
        let (names, rename_parameters) = match kind {
            Some("jad") => (
                Names::Jad(Default::default()),
                options.rename_parameters || options.jad_style_parameter_naming,
            ),
            Some("tiny") => (Names::Tiny(Default::default()), options.rename_parameters),
            _ => (Names::Identity, false),
        };
        Self {
            names,
            rename_parameters,
            parameters: Default::default(),
        }
    }

    pub(crate) fn parent_context(&self) -> Names {
        self.names.clone()
    }

    pub(crate) fn inherit(&mut self, parent: &Names) {
        match (&mut self.names, parent) {
            (Names::Jad(names), Names::Jad(parent)) => names.clone_from(parent),
            (Names::Tiny(names), Names::Tiny(parent)) => names.inherit(parent),
            _ => {}
        }
    }

    /// Both bundled providers visit variables in slot/version order. Parameters
    /// keep their first allocated name, including across later writer calls.
    pub(crate) fn rename<'a>(
        &mut self,
        method: &StructMethod,
        variables: impl Iterator<Item = (VarVersionPair, Option<&'a VarType>, &'a str)>,
    ) -> std::io::Result<FxHashMap<VarVersionPair, ArcStr>> {
        let mut result = FxHashMap::default();
        if matches!(self.names, Names::Identity) {
            return Ok(result);
        }
        let descriptor = MethodDescriptor::parse_descriptor(&method.descriptor);
        let limit = i32::from(!method.has_modifier(ACC_STATIC))
            + descriptor
                .params
                .iter()
                .map(|ty| ty.stack_size)
                .sum::<i32>();
        for (pair, ty, cast) in variables.sorted_unstable_by_key(|entry| entry.0) {
            let parameter = pair.var < limit;
            if parameter && !self.rename_parameters {
                continue;
            }
            let cleaned = cast.split('<').next().unwrap().rsplit('.').next().unwrap();
            if matches!(self.names, Names::Jad(_)) && cleaned == "this" {
                continue;
            }
            let name = if parameter && let Some(previous) = self.parameters.get(&pair.var) {
                previous.clone()
            } else {
                let name: ArcStr = match &mut self.names {
                    Names::Jad(names) => names.next(cleaned).into(),
                    Names::Tiny(names) => {
                        let Some(name) = names.next(method, ty, cleaned)? else {
                            continue;
                        };
                        name.into()
                    }
                    Names::Identity => unreachable!(),
                };
                if parameter {
                    self.parameters.insert(pair.var, name.clone());
                }
                name
            };
            result.insert(pair, name);
        }
        Ok(result)
    }
}
