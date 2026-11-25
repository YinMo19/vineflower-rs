// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Propagate stack assignments through SSAU use versions.

use std::{collections::VecDeque, mem, sync::Arc};

use rustc_hash::{FxHashMap, FxHashSet};

use super::StackSimplifyOptions;
use crate::decompiler::exps::{Expr, ExprKind, FunctionType, MonitorType};
use crate::decompiler::flow::{DirectEdgeType, DirectGraph, NodeType, flatten::build_direct_graph};
use crate::decompiler::ir::{ExprId, ExprListId, Ir, StatId};
use crate::decompiler::sforms::{Ssau, SsauResult};
use crate::decompiler::stats::{LoopType, StatementKind};
use crate::decompiler::vars::var_version_pair::VarVersionPair as Version;
use crate::decompiler::vars::version_graph::VarVersionsGraph;
use crate::engine::{Cx, counter_container::CounterContainer};
use crate::structs::attr::LocalVariable;
use crate::types::CodeType;
use crate::util::jhash::JHashSet;

type Replacements = FxHashMap<Version, ExprId>;
type Dependencies = FxHashMap<i32, FxHashSet<Version>>;

/// `StackVarsProcessor.iterateStatements` visits each direct node with the
/// replacements from the first incoming path. Tail expressions participate
/// both in their predecessor's list processing and in their own node visit.
pub(super) fn iterate_statements(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    root: StatId,
    ssau: &mut SsauResult,
    options: &StackSimplifyOptions,
) -> bool {
    let graph = build_direct_graph(&mut cx.ir, root);
    let mut inliner = Inliner {
        cx,
        counters,
        analysis: &mut ssau.versions,
        inline_regular_vars: options.inline_regular_vars,
        locals: FxHashMap::default(),
    };
    let mut changed = false;
    let mut visited = FxHashSet::default();
    let mut pending = VecDeque::from([(graph.first, Replacements::default())]);
    while let Some((id, mut values)) = pending.pop_front() {
        let node = &graph[id];
        if !visited.insert(&node.id) {
            continue;
        }
        let successors = node.successors(DirectEdgeType::Regular);
        let tail = match successors {
            [tail]
                if graph[*tail].ty == NodeType::Tail
                    && !inliner.cx.ir[graph[*tail].exprents].is_empty() =>
            {
                Some(&graph[*tail])
            }
            _ => None,
        };
        let lists = [
            (!inliner.cx.ir[node.exprents].is_empty()).then_some(node.exprents),
            tail.map(|tail| tail.exprents),
        ];
        let processed = tail.unwrap_or(node);
        let stat = processed.stat;

        let mut stage = 0;
        while stage < 2 {
            if !inliner.cx.options.simplify_stack {
                stage = 2;
            }
            for (position, list) in lists.into_iter().enumerate() {
                let Some(list) = list else { continue };
                let mut index = 0;
                while index < inliner.cx.ir[list].len() {
                    let next = inliner.cx.ir[list].get(index + 1).copied().or_else(|| {
                        lists
                            .get(position + 1)
                            .copied()
                            .flatten()
                            .map(|list| inliner.cx.ir[list][0])
                    });
                    let (next_index, updated) =
                        inliner.iterate_exprent(list, stat, index, next, &mut values, stage == 1);
                    index = next_index;
                    if updated {
                        changed = true;
                        stage = 2;
                    }
                }
            }
            stage += 1;
        }

        pending.extend(
            successors
                .iter()
                .map(|&successor| (successor, values.clone())),
        );

        // A cleared header list now represents Java's restored null entry.
        // A detached init node also reaches this check when it starts empty.
        let ir = &mut inliner.cx.ir;
        if matches!(
            processed.ty,
            NodeType::Init | NodeType::Condition | NodeType::Increment
        ) && ir[processed.exprents].is_empty()
            && let StatementKind::Do(loop_stat) = ir[stat].kind
            && loop_stat.ty == LoopType::For
            && loop_stat.init(ir).is_none()
            && loop_stat.increment(ir).is_none()
        {
            stat.set_loop_type(ir, LoopType::While);
        }
    }
    inliner.apply_locals(&graph);
    changed
}

struct Inliner<'a> {
    cx: &'a mut Cx,
    counters: &'a mut CounterContainer,
    analysis: &'a mut Ssau,
    inline_regular_vars: bool,
    locals: FxHashMap<Version, Arc<LocalVariable>>,
}

#[derive(Clone, Copy)]
enum ChildReplacement {
    Read(ExprId),
    Assignment(ExprId),
}

impl Inliner<'_> {
    fn iterate_exprent(
        &mut self,
        list: ExprListId,
        stat: StatId,
        index: usize,
        mut next: Option<ExprId>,
        values: &mut Replacements,
        across_stack: bool,
    ) -> (usize, bool) {
        let expr = self.cx.ir[list][index];
        let changed = self.iterate_children(expr, expr, next, values);
        let advance = (index + 1, changed);
        if let Some(pair) = variable_version(&self.cx.ir, expr) {
            return if let Some(&value) = values.get(&pair) {
                self.cx.ir[list][index] = value;
                (index + 1, true)
            } else {
                (index + 1, false)
            };
        }
        let Some((left, right, pair, stack)) = simple_assignment(&self.cx.ir, expr) else {
            return advance;
        };
        let (used, not_dominated) = used_versions(&self.analysis.graph, pair);
        if !not_dominated && used.is_empty() {
            let kind = &self.cx.ir[right].kind;
            let standalone = match kind {
                ExprKind::Invocation(_) | ExprKind::Assignment { .. } => true,
                ExprKind::New { new_type, .. } => {
                    new_type.array_dim <= 0 && new_type.ty == CodeType::Object
                }
                _ => false,
            };
            if stack && standalone {
                self.cx.ir[list][index] = right;
                return (index + 1, true);
            }
            match kind {
                ExprKind::Variable(_) => self.on_deleted_var(stat, left, right),
                ExprKind::Function {
                    op: FunctionType::Ipp | FunctionType::Imm,
                    ..
                } if stack => {
                    self.cx.ir[list][index] = right;
                    return (index, true);
                }
                ExprKind::Function {
                    op: FunctionType::Cast,
                    operands,
                    ..
                } if stack && !matches!(self.cx.ir[operands[0]].kind, ExprKind::Invocation(_)) => {}
                ExprKind::Field(_) if stack => {}
                _ => return advance,
            }
            self.cx.ir[list].remove(index);
            return (index, true);
        }

        let catch_temp =
            matches!(&self.cx.ir[right].kind, ExprKind::Variable(var) if var.catch_temp);
        if !stack && !self.inline_regular_vars && !catch_temp {
            return advance;
        }
        if Expr::usage(&self.cx.ir, right) & Expr::MULTIPLE_USES == 0
            && (not_dominated || used.len() > 1)
        {
            return advance;
        }

        let mut dependencies = self.all_var_versions(pair, right);
        let self_reference = dependencies.contains_key(&pair.var);
        if self_reference && not_dominated {
            return advance;
        }
        if across_stack {
            next = simplify_across_stack(self.cx, list, index, next, right, pair.var).or(next);
        }
        let next_versions = next.map(|next| all_versions(&self.cx.ir, next));
        let simple_value = matches!(
            self.cx.ir[right].kind,
            ExprKind::Constant { .. } | ExprKind::Variable(_)
        );
        if self_reference
            && !simple_value
            && next_versions
                .as_ref()
                .is_some_and(|next| used.iter().any(|version| !next.contains(version)))
        {
            return advance;
        }
        dependencies.remove(&pair.var);

        let mut replacements = JHashSet::new();
        let mut kept = false;
        for version in used {
            if self.is_version_to_be_replaced(version, &dependencies, pair)
                && (simple_value
                    || matches!(self.cx.ir[right].kind, ExprKind::Field(_))
                    || next_versions
                        .as_ref()
                        .is_none_or(|next| next.contains(&version)))
            {
                replacements.insert(version);
            } else {
                kept = true;
            }
        }
        if self_reference && kept {
            return advance;
        }
        self.copy_replacements(right, &replacements, values);
        if !not_dominated && !kept {
            self.on_deleted_var(stat, left, right);
            self.cx.ir[list].remove(index);
            (index, true)
        } else {
            advance
        }
    }

    fn iterate_children(
        &mut self,
        expr: ExprId,
        parent: ExprId,
        next: Option<ExprId>,
        values: &mut Replacements,
    ) -> bool {
        let mut changed = false;
        // Capture Java's immediate-child list, including repeated aliases.
        let children: Vec<_> = Expr::children(&self.cx.ir, expr).collect();
        for mut child in children {
            loop {
                let (replacement, updated) = self.iterate_child(child, parent, next, values);
                changed |= updated;
                match replacement {
                    Some(ChildReplacement::Read(replacement)) => {
                        self.replace_single_var(expr, child, replacement);
                        child = replacement;
                        changed = true;
                    }
                    Some(ChildReplacement::Assignment(replacement)) => {
                        Expr::replace(&mut self.cx.ir, expr, child, replacement);
                        let bytecode = self.cx.ir[child].bytecode.clone();
                        Expr::add_offsets(&mut self.cx.ir, replacement, bytecode.as_ref());
                        changed = true;
                        break;
                    }
                    None => break,
                }
            }
        }
        changed
    }

    fn iterate_child(
        &mut self,
        expr: ExprId,
        parent: ExprId,
        next: Option<ExprId>,
        values: &mut Replacements,
    ) -> (Option<ChildReplacement>, bool) {
        let changed = self.iterate_children(expr, parent, next, values);
        if let Some(value) = variable_version(&self.cx.ir, expr).and_then(|pair| values.get(&pair))
        {
            return (Some(ChildReplacement::Read(*value)), true);
        }
        let unchanged = (None, changed);
        let Some((_, right, pair, stack)) = simple_assignment(&self.cx.ir, expr) else {
            return unchanged;
        };
        let synchronized_head = next.is_none()
            && matches!(self.cx.ir[parent].kind, ExprKind::Monitor { kind: MonitorType::Enter, value, .. }
                if Expr::equals(self.cx, expr, value));
        if !stack && !self.inline_regular_vars && !synchronized_head {
            return unchanged;
        }
        let (used, not_dominated) = used_versions(&self.analysis.graph, pair);
        let replace = (Some(ChildReplacement::Assignment(right)), changed);
        if !not_dominated && used.is_empty() {
            return replace;
        }
        let both = Expr::MULTIPLE_USES | Expr::SIDE_EFFECTS_FREE;
        if !stack || Expr::usage(&self.cx.ir, right) & both != both {
            return unchanged;
        }
        let mut dependencies = self.all_var_versions(pair, right);
        if dependencies.remove(&pair.var).is_some() && not_dominated {
            return unchanged;
        }
        let mut allowed = all_versions(&self.cx.ir, parent);
        if let Some(next) = next {
            allowed.extend(all_versions(&self.cx.ir, next).iter().copied());
        }
        let mut replacements = JHashSet::new();
        let mut kept = false;
        for version in used {
            if self.is_version_to_be_replaced(version, &dependencies, pair)
                && (matches!(self.cx.ir[right].kind, ExprKind::Variable(_))
                    || allowed.contains(&version))
            {
                replacements.insert(version);
            } else {
                kept = true;
            }
        }
        if not_dominated || kept {
            return unchanged;
        }
        self.copy_replacements(right, &replacements, values);
        replace
    }

    fn replace_single_var(&mut self, parent: ExprId, old: ExprId, new: ExprId) {
        Expr::replace(&mut self.cx.ir, parent, old, new);
        let offsets = self.cx.ir[old].bytecode.clone();
        Expr::add_offsets(&mut self.cx.ir, new, offsets.as_ref());

        let source = variable_version(&self.cx.ir, old).unwrap();
        let source_node = self.analysis.graph.get(source);
        let source_known = source_node.is_some();
        let mut source_live = source_node.and_then(|node| node.live.clone());
        for &pair in all_versions(&self.cx.ir, new).iter() {
            let Some(live) = &mut self.analysis.graph[pair].live else {
                continue;
            };
            assert!(source_known, "Missing live-version source for {source}");
            if pair == source {
                // The source and destination live maps alias in this case.
                live.retain(|_, _| false);
                source_live = None;
            } else {
                live.retain(|key, versions| {
                    let Some(source) = source_live.as_ref().and_then(|live| live.get(key)) else {
                        return false;
                    };
                    versions.complement(source);
                    !versions.is_empty()
                });
            }
        }
    }

    fn on_deleted_var(&mut self, mut stat: StatId, left: ExprId, right: ExprId) {
        let ir = &mut self.cx.ir;
        let (ExprKind::Variable(left), ExprKind::Variable(right)) =
            (&ir[left].kind, &ir[right].kind)
        else {
            return;
        };
        let Some(lvt) = left.lvt.clone().filter(|_| right.lvt.is_none()) else {
            return;
        };
        let index = right.index;
        let mut queue = VecDeque::from([Version::new(left.index, left.version)]);
        let mut seen = FxHashSet::default();
        while let Some(pair) = queue.pop_front() {
            seen.insert(pair);
            if pair.var == index {
                self.locals.insert(pair, Arc::clone(&lvt));
            }
            let node = &self.analysis.graph[pair];
            let assigned = self.analysis.assignments.get(&pair).filter(|&&source| {
                !node.predecessors.contains(&source) && self.analysis.graph.get(source).is_some()
            });
            queue.extend(
                node.predecessors
                    .iter()
                    .chain(assigned)
                    .copied()
                    .filter(|pred| !seen.contains(pred)),
            );
        }

        while let Some(parent) = ir[stat].parent {
            if let StatementKind::Catch { vars, .. } = &ir[parent].kind {
                for expr in vars.clone() {
                    if matches!(&ir[expr].kind, ExprKind::Variable(var) if var.index == index) {
                        Expr::set_local_variable(ir, expr, Arc::clone(&lvt));
                    }
                }
                break;
            }
            stat = parent;
        }
    }

    fn apply_locals(&mut self, graph: &DirectGraph) {
        if self.locals.is_empty() {
            return;
        }
        let ir = &mut self.cx.ir;
        for id in graph.regular_breadth_first() {
            let node = &graph[id];
            for index in 0..ir[node.exprents].len() {
                let expr = ir[node.exprents][index];
                for child in Expr::all_exprents(ir, expr, true, true) {
                    if let ExprKind::Variable(var) = &ir[child].kind
                        && var.lvt.is_none()
                        && let Some(lvt) = self.locals.get(&Version::new(var.index, var.version))
                    {
                        Expr::set_local_variable(ir, child, Arc::clone(lvt));
                    }
                }
            }
        }
    }

    fn copy_replacements(
        &mut self,
        right: ExprId,
        eligible: &JHashSet<Version>,
        values: &mut Replacements,
    ) {
        for &version in eligible.iter() {
            let copy = Expr::copy(self.cx, self.counters, right);
            if matches!(self.cx.ir[right].kind, ExprKind::Field(_))
                && let Some(&field) = self.analysis.field_vars.get(&self.cx.ir[right].id)
            {
                self.analysis.field_vars.insert(self.cx.ir[copy].id, field);
            }
            values.insert(version, copy);
        }
    }

    fn is_version_to_be_replaced(
        &self,
        used: Version,
        dependencies: &Dependencies,
        defined: Version,
    ) -> bool {
        let graph = &self.analysis.graph;
        let node = &graph[used];
        if node.phantom_node.is_some()
            || self.analysis.first_range.get(&defined) != self.analysis.first_range.get(&used)
        {
            return false;
        }
        // A known node without a recorded live map has an empty map upstream.
        dependencies.iter().all(|(&var, dominators)| {
            node.live
                .as_ref()
                .and_then(|live| live.get(var))
                .is_some_and(|versions| {
                    versions.iter().all(|version| {
                        graph.is_dominator_set(Version::new(var, version), dominators)
                    })
                })
        })
    }

    fn all_var_versions(&self, defined: Version, expr: ExprId) -> Dependencies {
        let ir = &self.cx.ir;
        let live = self
            .analysis
            .graph
            .get(defined)
            .and_then(|node| node.live.as_ref());
        let mut dependencies = FxHashMap::default();
        for child in Expr::all_exprents(ir, expr, true, true) {
            match &ir[child].kind {
                ExprKind::Variable(var) if var.index == defined.var => {
                    dependencies.entry(defined.var).or_default();
                }
                ExprKind::Variable(var) => {
                    let versions = live
                        .and_then(|map| map.get(var.index))
                        .expect("inconsistent live map!");
                    dependencies.insert(
                        var.index,
                        versions
                            .iter()
                            .map(|v| Version::new(var.index, v))
                            .collect(),
                    );
                }
                ExprKind::Field(_) => {
                    if let Some(&index) = self.analysis.field_vars.get(&ir[child].id)
                        && let Some(versions) = live.and_then(|map| map.get(index))
                    {
                        dependencies.insert(
                            index,
                            versions.iter().map(|v| Version::new(index, v)).collect(),
                        );
                    }
                }
                _ => {}
            }
        }
        dependencies
    }
}

fn simple_assignment(ir: &Ir, expr: ExprId) -> Option<(ExprId, ExprId, Version, bool)> {
    let ExprKind::Assignment {
        left,
        right,
        compound: None,
    } = ir[expr].kind
    else {
        return None;
    };
    let ExprKind::Variable(var) = &ir[left].kind else {
        return None;
    };
    (!var.effectively_final).then_some((
        left,
        right,
        Version::new(var.index, var.version),
        var.stack,
    ))
}

fn variable_version(ir: &Ir, expr: ExprId) -> Option<Version> {
    match &ir[expr].kind {
        ExprKind::Variable(var) => Some(Version::new(var.index, var.version)),
        _ => None,
    }
}

fn all_versions(ir: &Ir, expr: ExprId) -> JHashSet<Version> {
    let mut versions = JHashSet::new();
    versions.extend(
        Expr::all_exprents(ir, expr, true, true)
            .into_iter()
            .filter_map(|child| variable_version(ir, child)),
    );
    versions
}

fn used_versions(graph: &VarVersionsGraph, defined: Version) -> (Vec<Version>, bool) {
    let mut visited = FxHashSet::default();
    let mut not_dominated = FxHashSet::default();
    let mut used = Vec::new();
    let mut pending = VecDeque::from([defined]);
    while let Some(pair) = pending.pop_front() {
        visited.insert(pair);
        if pair != defined {
            used.push(pair);
        }
        for &successor in &graph[pair].successors {
            if visited.contains(&successor) {
                continue;
            }
            if graph[successor]
                .predecessors
                .iter()
                .all(|pred| visited.contains(pred))
            {
                pending.push_back(successor);
            } else {
                not_dominated.insert(successor);
            }
        }
    }
    (
        used,
        not_dominated.iter().any(|pair| !visited.contains(pair)),
    )
}

fn simplify_across_stack(
    cx: &Cx,
    list: ExprListId,
    index: usize,
    next: Option<ExprId>,
    right: ExprId,
    left: i32,
) -> Option<ExprId> {
    let following = cx.ir[list].get(index + 2).copied()?;
    let ExprKind::Assignment {
        right: next_right, ..
    } = cx.ir[next?].kind
    else {
        return None;
    };
    let rhs = Expr::all_exprents(&cx.ir, right, true, false);
    if rhs.is_empty() {
        return None;
    }
    let after = Expr::all_exprents(&cx.ir, next_right, true, false);
    if after.len() == rhs.len() && trees_equal(cx, left, &rhs, &after) {
        return Some(following);
    }
    if after.len() > rhs.len()
        && after.into_iter().any(|child| {
            let subtree = Expr::all_exprents(&cx.ir, child, true, false);
            subtree.len() == rhs.len() && trees_equal(cx, left, &rhs, &subtree)
        })
    {
        return Some(following);
    }
    None
}

fn trees_equal(cx: &Cx, assigned: i32, left: &[ExprId], right: &[ExprId]) -> bool {
    left.iter().zip(right).all(|(&a, &b)| {
        let first = &cx.ir[a].kind;
        let second = &cx.ir[b].kind;
        match (first, second) {
            (ExprKind::Variable(a), ExprKind::Variable(b)) => {
                a.index == b.index && b.index != assigned
            }
            (ExprKind::Field(a), ExprKind::Field(b)) => {
                a.name == b.name
                    && a.classname == b.classname
                    && a.is_static() == b.is_static()
                    && a.descriptor == b.descriptor
            }
            (ExprKind::Constant { .. }, ExprKind::Constant { .. }) => Expr::equals(cx, a, b),
            _ => mem::discriminant(first) == mem::discriminant(second),
        }
    })
}
