// Copyright 2000-2024 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! SFormsConstructor's fixed-point iteration. Each sweep visits the entire
//! direct graph in its stored order. A change schedules another sweep only
//! when the affected successor has already been passed or is the current node.

use std::borrow::Cow;

use arcstr::ArcStr;
use rustc_hash::{FxHashMap, FxHashSet};

use super::{
    Transfer, VarMapHolder, VariableVersions, Version, VersionAnalysis, VersionMap, variable,
};
use crate::code::code_constants::ACC_STATIC;
use crate::decompiler::exps::{ExprKind, STACK_BASE};
use crate::decompiler::flow::{
    DirectEdgeType, DirectGraph, DirectId, NodeType, flatten::build_direct_graph,
};
use crate::decompiler::ir::{Ir, StatId};
use crate::decompiler::stats::StatementKind;
use crate::engine::method_timeout::checkpoint;
use crate::structs::StructMethod;
use crate::types::MethodDescriptor;
use crate::util::fast_sparse_set::FastSparseSetFactory;

pub(super) fn split<A: VersionAnalysis>(
    ir: &mut Ir,
    root: StatId,
    method: &StructMethod,
    mut analysis: A,
) -> Result<VariableVersions<A>, Version> {
    let graph = build_direct_graph(ir, root);
    let factory = FastSparseSetFactory::new(0..64);
    let mut entry = VersionMap::new(&factory);
    let mut index = 0;
    if method.access_flags & ACC_STATIC == 0 {
        entry.set_current(index, analysis.init_parameter(index, false));
        index += 1;
    }
    for parameter in MethodDescriptor::parse_descriptor(&method.descriptor).params {
        entry.set_current(index, analysis.init_parameter(index, false));
        index += parameter.stack_size;
    }
    let mut flow = FlowState::new(factory);
    flow.seeds.insert(graph[graph.first].id.clone(), entry);
    flow.seed_handlers(ir, root, &graph, &mut analysis);
    let extra = graph.extra_nodes.iter().map(|&id| &graph[id].id).collect();
    while flow.sweep(ir, &graph, &extra, &mut analysis, false)? {}
    if A::CALCULATE_LIVENESS {
        flow.sweep(ir, &graph, &extra, &mut analysis, true)?;
    }
    Ok(VariableVersions {
        graph,
        versions: analysis,
        read_counts: flow.reads,
    })
}

type NodeMaps = FxHashMap<ArcStr, VersionMap>;

struct FlowState {
    factory: FastSparseSetFactory<i32>,
    inputs: NodeMaps,
    outputs: FxHashMap<ArcStr, VarMapHolder>,
    seeds: NodeMaps,
    catchable: NodeMaps,
    reads: FxHashMap<Version, i32>,
}

impl FlowState {
    fn new(factory: FastSparseSetFactory<i32>) -> Self {
        Self {
            factory,
            inputs: NodeMaps::default(),
            outputs: FxHashMap::default(),
            seeds: NodeMaps::default(),
            catchable: NodeMaps::default(),
            reads: FxHashMap::default(),
        }
    }

    fn seed_handlers(
        &mut self,
        ir: &Ir,
        root: StatId,
        graph: &DirectGraph,
        analysis: &mut impl VersionAnalysis,
    ) {
        let mut pending = vec![root];
        while let Some(stat) = pending.pop() {
            let statement = &ir[stat];
            if let StatementKind::Catch { vars, .. } | StatementKind::CatchAll { vars, .. } =
                &statement.kind
            {
                for (&handler, &expr) in statement.stats[1..].iter().zip(vars) {
                    let index = variable(ir, expr).var;
                    let mut seed = VersionMap::new(&self.factory);
                    seed.set_current(index, analysis.init_parameter(index, true));
                    let node = graph.direct_node(handler).expect("Missing catch node");
                    self.seeds.insert(graph[node].id.clone(), seed);
                }
            }
            pending.extend(statement.stats.iter().rev().copied());
        }
    }

    fn sweep(
        &mut self,
        ir: &mut Ir,
        graph: &DirectGraph,
        extra: &FxHashSet<&ArcStr>,
        analysis: &mut impl VersionAnalysis,
        live: bool,
    ) -> Result<bool, Version> {
        let mut updated = FxHashSet::default();
        for &id in &graph.order {
            checkpoint();
            let node = &graph[id];
            updated.remove(&node.id);
            let input = self.merge_inputs(ir, graph, id);
            self.inputs.insert(node.id.clone(), input.clone());
            let catchable = if node.successors(DirectEdgeType::Exception).is_empty() {
                None
            } else {
                let mut locals = input.clone();
                locals.clear_stacks();
                locals.clear_fields();
                Some(
                    self.catchable
                        .entry(node.id.clone())
                        .insert_entry(locals)
                        .into_mut(),
                )
            };
            let mut maps = VarMapHolder::normal(input);
            let mut transfer = Transfer {
                analysis,
                stat: node.stat,
                live,
                catchable,
                reads: &mut self.reads,
            };
            if ir[node.exprents].is_empty()
                && let StatementKind::Do(loop_stat) = ir[node.stat].kind
            {
                // The FOR init node is detached when the statement's init is
                // null. Other active headers still contain a null in Java,
                // which SForms attempts to process as an expression.
                let active_header = match node.ty {
                    NodeType::Init => loop_stat.init == Some(node.exprents),
                    NodeType::Condition | NodeType::Increment | NodeType::ForeachVardef => true,
                    _ => false,
                };
                assert!(!active_header, "Loop header {} has no expression", node.id);
            }
            if node.ty == NodeType::ForeachVardef
                && let Some(&var) = ir[node.exprents].first()
                && matches!(ir[var].kind, ExprKind::Variable(_))
            {
                transfer.assign(ir, var, maps.normal_mut());
            } else {
                for index in 0..ir[node.exprents].len() {
                    let expr = ir[node.exprents][index];
                    maps.merge_branches();
                    transfer.process(ir, expr, &mut maps);
                    if transfer.analysis.missing_version().is_some() {
                        break;
                    }
                }
            }
            if let Some(missing) = transfer.analysis.missing_version() {
                return Err(missing);
            }

            let negative = graph.neg_if_branch.contains_key(&id);
            let changed = self.outputs.get(&node.id).is_none_or(|old| {
                old.if_true() != maps.if_true() || negative && old.if_false() != maps.if_false()
            });
            if changed {
                self.outputs.insert(node.id.clone(), maps);
                if !extra.contains(&node.id) {
                    updated.extend(
                        node.successors(DirectEdgeType::Regular)
                            .iter()
                            .chain(node.successors(DirectEdgeType::Exception))
                            .map(|&next| &graph[next].id),
                    );
                }
            }
        }
        Ok(!updated.is_empty())
    }

    fn merge_inputs(&self, ir: &Ir, graph: &DirectGraph, id: DirectId) -> VersionMap {
        let node = &graph[id];
        let mut input = VersionMap::new(&self.factory);
        for &pred in node.predecessors(DirectEdgeType::Regular) {
            let versions = self.filtered_output(ir, graph, id, pred);
            if input.is_empty() {
                input = versions.into_owned();
            } else {
                input.union(&versions);
            }
        }
        for map in node
            .predecessors(DirectEdgeType::Exception)
            .iter()
            .filter_map(|&pred| self.catchable.get(&graph[pred].id))
            .chain(self.seeds.get(&node.id))
        {
            if input.is_empty() {
                input.clone_from(map);
            } else {
                input.union(map);
            }
        }
        input
    }

    fn filtered_output(
        &self,
        ir: &Ir,
        graph: &DirectGraph,
        dest: DirectId,
        pred: DirectId,
    ) -> Cow<'_, VersionMap> {
        let node = &graph[dest];
        let pred_node = &graph[pred];
        let mut output = match self.outputs.get(&pred_node.id) {
            None => Cow::Owned(VersionMap::new(&self.factory)),
            Some(maps)
                if graph
                    .neg_if_branch
                    .get(&pred)
                    .is_some_and(|&negative| graph[negative].id == node.id) =>
            {
                Cow::Borrowed(maps.if_false())
            }
            Some(maps) => Cow::Borrowed(maps.if_true()),
        };

        let mut scope = pred_node.try_finally;
        let entering_try = node
            .try_finally
            .is_some_and(|id| graph[id].ty == NodeType::Finally && graph[id].try_finally == scope);
        if !entering_try && pred_node.ty != NodeType::Finally {
            while scope != node.try_finally {
                let finally = &graph[scope.expect("Inconsistent finally scope")];
                if finally.ty == NodeType::Finally {
                    // The pinned Java lookup uses the uppercase enum name here,
                    // although DirectNode normally creates lowercase suffixes.
                    let input_id = format!("{}_FINALLY", ir[finally.stat].id);
                    if let (Some(before), Some(after)) = (
                        self.inputs.get(input_id.as_str()),
                        self.outputs.get(&finally.id),
                    ) {
                        apply_diff(before, after.if_true(), output.to_mut());
                    }
                }
                scope = finally.try_finally;
            }
        }
        output
    }
}

fn apply_diff(input: &VersionMap, output: &VersionMap, target: &mut VersionMap) {
    for (key, versions) in input
        .iter()
        .filter(|(key, set)| *key < STACK_BASE && !set.is_empty())
    {
        let Some(writes) = output.get(key) else {
            continue;
        };
        let first = versions.iter().next().unwrap();
        if writes.contains(&first) {
            let mut added = writes.clone();
            added.complement(versions);
            if !added.is_empty() {
                target
                    .get_mut(key)
                    .expect("Missing incoming version")
                    .union(&added);
            }
        } else {
            target.put(key, versions.clone());
        }
    }
    for (key, writes) in output
        .iter()
        .filter(|(key, set)| *key < STACK_BASE && !set.is_empty())
    {
        if input.get(key).is_none_or(|set| set.is_empty()) {
            target.put(key, writes.clone());
        }
    }
}
