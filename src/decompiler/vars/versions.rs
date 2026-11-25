// Copyright 2000-2017 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Per-method variable types and slot provenance retained by VarVersionsProcessor.

use std::io;

use rustc_hash::FxHashMap;

use super::var_version_pair::VarVersionPair as Version;
use crate::decompiler::exps::ExprKind;
use crate::decompiler::ir::{StatId, VarProcessorId};
use crate::decompiler::{flow::flatten::build_direct_graph, sforms::split_ssa};
use crate::engine::{
    Cx,
    counter_container::{CounterContainer, VAR_COUNTER},
};
use crate::structs::StructClass;
use crate::types::{CodeType, MethodDescriptor, VarType};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FinalType {
    NonFinal,
    ExplicitFinal,
    Final,
}

#[derive(Default)]
pub struct VarVersions {
    pub lower: FxHashMap<Version, VarType>,
    /// Java keeps a null entry when a numbered variable had no upper bound.
    pub upper: FxHashMap<Version, Option<VarType>>,
    pub final_vars: FxHashMap<Version, FinalType>,
    pub original: FxHashMap<i32, Version>,
    pub(crate) initialized: bool,
}

impl VarVersions {
    fn eliminate_non_java_types(&mut self) {
        for (pair, ty) in &mut self.lower {
            *ty = match ty.ty {
                CodeType::Bytechar | CodeType::Shortchar => {
                    if self
                        .upper
                        .get(pair)
                        .and_then(Option::as_ref)
                        .is_some_and(|ty| ty.ty == CodeType::Char)
                    {
                        VarType::VARTYPE_CHAR
                    } else if ty.ty == CodeType::Bytechar {
                        VarType::VARTYPE_BYTE
                    } else {
                        VarType::VARTYPE_SHORT
                    }
                }
                CodeType::Null => VarType::VARTYPE_OBJECT,
                _ => continue,
            };
        }
    }

    fn assign_indices(&mut self, counters: &mut CounterContainer) -> FxHashMap<Version, i32> {
        let mut pairs: Vec<_> = self
            .lower
            .keys()
            .filter(|pair| pair.version >= 0)
            .copied()
            .collect();
        pairs.sort_unstable();

        let mut indices = FxHashMap::default();
        for pair in pairs {
            let index = if pair.version == 1 {
                pair.var
            } else {
                counters.get_counter_and_increment(VAR_COUNTER)
            };
            let new = Version::new(index, 0);
            self.lower.insert(new, self.lower[&pair].clone());
            self.upper
                .insert(new, self.upper.get(&pair).cloned().flatten());
            if let Some(final_type) = self.final_vars.remove(&pair) {
                self.final_vars.insert(new, final_type);
            }
            indices.insert(pair, index);
            self.original.insert(index, pair);
        }
        indices
    }
}

pub(crate) fn set_versions(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    root: StatId,
    owner: VarProcessorId,
    class: &StructClass,
    descriptor: &MethodDescriptor,
) -> io::Result<()> {
    let previous = std::mem::replace(
        &mut cx.ir[owner],
        VarVersions {
            initialized: true,
            ..VarVersions::default()
        },
    )
    .original;
    let method = std::sync::Arc::clone(root.method(&cx.ir));
    let ssa = split_ssa(&mut cx.ir, root, &method);
    let graph = build_direct_graph(&mut cx.ir, root);
    let reps = ssa.versions.phi_representatives();
    // No pass below changes the shape of an expression. Preserve repeated
    // visits to shared nodes when applying the upstream graph traversal.
    let expressions = graph.deep_exprents(&cx.ir);
    for &id in &expressions {
        if let ExprKind::Variable(var) = &mut cx.ir[id].kind
            && let Some(&version) = reps.get(&var.pair())
        {
            var.version = version;
        }
    }

    super::inference::calculate(cx, counters, root, &expressions, owner, class, descriptor)?;
    cx.ir[owner].eliminate_non_java_types();
    let indices = cx.ir[owner].assign_indices(counters);
    let types = &cx.ir.variable_processors[owner];
    for id in expressions {
        let expr = &mut cx.ir.exprs[id];
        match &mut expr.kind {
            ExprKind::Variable(var) => {
                if let Some(&index) = indices.get(&var.pair()) {
                    var.index = index;
                    var.version = 0;
                }
            }
            ExprKind::Constant { var_type, .. } => {
                if let Some(Some(upper)) = types.upper.get(&Version::new(expr.id, -1)) {
                    var_type.clone_from(upper);
                }
            }
            _ => {}
        }
    }
    for pair in cx.ir[owner].original.values_mut() {
        if let Some(&old) = previous.get(&pair.var) {
            *pair = old;
        }
    }
    Ok(())
}
