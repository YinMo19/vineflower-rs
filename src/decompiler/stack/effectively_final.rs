// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Relate captured constructor arguments to the local assignments that must
//! remain effectively final. This runs only on the first SSAU graph.

use std::collections::VecDeque;

use rustc_hash::{FxHashMap, FxHashSet};

use crate::code::code_constants::INIT_NAME;
use crate::decompiler::exps::{Expr, ExprKind, STACK_BASE};
use crate::decompiler::ir::{ExprId, ExprListId, Ir, StatId};
use crate::decompiler::sforms::Ssau;
use crate::decompiler::vars::{
    var_version_pair::VarVersionPair as Version, version_graph::VarVersionsGraph,
};
use crate::engine::{
    Cx,
    class_nodes::{ClassNodes, LambdaInformation},
};
use crate::types::{MethodDescriptor, VarType};

pub(super) fn mark(cx: &mut Cx, root: StatId, ssau: &Ssau) {
    let mut scan = Scan {
        ir: &mut cx.ir,
        classes: &cx.class_nodes,
        ssau,
        definitions: FxHashMap::default(),
    };
    let mut pending = vec![root];
    while let Some(stat) = pending.pop() {
        if let Some(list) = scan.ir[stat].exprents {
            for index in 0..scan.ir[list].len() {
                scan.expression(scan.ir[list][index], list, index);
            }
        }
        pending.extend(scan.ir[stat].stats.iter().rev().copied());
    }
}

struct Scan<'a> {
    ir: &'a mut Ir,
    classes: &'a ClassNodes,
    ssau: &'a Ssau,
    definitions: FxHashMap<Version, ExprId>,
}

impl Scan<'_> {
    fn expression(&mut self, expr: ExprId, list: ExprListId, index: usize) {
        match &self.ir[expr].kind {
            ExprKind::Assignment { left, .. } => {
                if let ExprKind::Variable(var) = &self.ir[*left].kind {
                    self.definitions
                        .insert(Version::new(var.index, var.version), *left);
                }
            }
            ExprKind::New {
                anonymous: true,
                new_type,
                lambda,
                method_reference,
                constructor,
                ..
            } => {
                if let Some(node) = self.classes.get(new_type.name()) {
                    if !lambda {
                        if let Some(init) = node
                            .class
                            .methods
                            .iter()
                            .find(|method| method.name == INIT_NAME)
                        {
                            let params =
                                MethodDescriptor::parse_descriptor(&init.descriptor).params;
                            for pos in index.saturating_sub(params.len())..index {
                                let preceding = self.ir[list][pos];
                                if let ExprKind::Assignment { left, .. } = self.ir[preceding].kind
                                    && let ExprKind::Variable(var) = &mut self.ir[left].kind
                                    && var
                                        .lvt
                                        .as_ref()
                                        .is_some_and(|lvt| params.contains(&lvt.get_var_type()))
                                {
                                    var.effectively_final = true;
                                }
                            }
                        }
                    } else if !method_reference {
                        self.lambda_captures(node.lambda.as_ref().unwrap(), constructor.unwrap());
                    }
                }
            }
            _ => {}
        }
        let children: Vec<_> = Expr::children(self.ir, expr).collect();
        for child in children {
            self.expression(child, list, index);
        }
    }

    fn lambda_captures(&mut self, lambda: &LambdaInformation, constructor: ExprId) {
        let content = MethodDescriptor::parse_descriptor(&lambda.content_method_descriptor);
        let interface = MethodDescriptor::parse_descriptor(&lambda.method_descriptor);
        let count = content.params.len().saturating_sub(interface.params.len());
        let offset = usize::from(!lambda.is_content_method_static);
        for (i, ty) in content.params.iter().take(count).enumerate() {
            let ExprKind::Invocation(invocation) = &self.ir[constructor].kind else {
                unreachable!()
            };
            let param = invocation.parameters[offset + i];
            if let ExprKind::Variable(var) = &self.ir[param].kind
                && let Some(version) =
                    capture_definition(self.ssau, Version::new(var.index, var.version), ty)
                && let Some(&definition) = self.definitions.get(&version)
                && let ExprKind::Variable(var) = &mut self.ir[definition].kind
            {
                var.effectively_final = true;
            }
        }
    }
}

fn capture_definition(ssau: &Ssau, param: Version, ty: &VarType) -> Option<Version> {
    let graph = &ssau.graph;
    let mut node = graph.get(param)?;
    let mut definition = param;
    loop {
        let source = if node.var >= STACK_BASE {
            node.single_predecessor()
        } else {
            let roots = reaching_roots(graph, node.as_pair());
            let candidates = graph
                .nodes
                .iter()
                .filter(|other| {
                    other.var == node.var
                        && other.predecessors.is_empty()
                        && other.lvt.as_ref().map_or_else(
                            || other.version > node.version,
                            |lvt| lvt.get_var_type() == *ty,
                        )
                })
                .count();
            if roots.len() < candidates {
                break;
            }
            match roots.as_slice() {
                [root] => {
                    definition = *root;
                    *root
                }
                [first, second] => {
                    if let (Some(a), Some(b)) = (&graph[*first].lvt, &graph[*second].lvt)
                        && a.get_version() == b.get_version()
                    {
                        definition = a.get_version();
                    }
                    break;
                }
                _ => break,
            }
        };
        let Some(&next) = ssau.assignments.get(&source) else {
            break;
        };
        if next.var < 0 {
            return Some(next);
        }
        let Some(next) = graph.get(next) else { break };
        node = next;
    }
    Some(definition)
}

fn reaching_roots(graph: &VarVersionsGraph, start: Version) -> Vec<Version> {
    let mut roots = Vec::new();
    let mut seen = FxHashSet::default();
    let mut pending = VecDeque::from([start]);
    seen.insert(start);
    while let Some(version) = pending.pop_front() {
        let parents = &graph[version].predecessors;
        if parents.is_empty() {
            roots.push(version);
        } else {
            pending.extend(
                parents
                    .iter()
                    .copied()
                    .filter(|parent| seen.insert(*parent)),
            );
        }
    }
    roots
}
