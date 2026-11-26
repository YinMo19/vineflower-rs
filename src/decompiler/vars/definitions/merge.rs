// Copyright 2000-2024 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Reunite compatible versions of one bytecode local after SSA numbering.

use std::{collections::VecDeque, io};

use arcstr::ArcStr;
use indexmap::IndexMap;
use rustc_hash::{FxHashMap, FxHashSet};

use crate::code::code_constants::ACC_STATIC;
use crate::decompiler::exps::{ExitType, Expr, ExprKind};
use crate::decompiler::ir::{ExprId, Ir, StatId, VarProcessorId};
use crate::decompiler::sforms::{reset_versions, try_split_ssau};
use crate::decompiler::stats::StatementKind;
use crate::decompiler::vars::var_version_pair::VarVersionPair as Version;
use crate::engine::Cx;
use crate::structs::StructMethod;
use crate::types::{CodeType, MethodDescriptor, TypeFamily, VarType};

type Scope = FxHashMap<Option<i32>, Version>;
type Denylist = FxHashMap<Version, Version>;
type Sources = IndexMap<ExprId, FxHashSet<ExprId>>;

#[derive(Clone, Copy)]
struct Candidate {
    from: Version,
    to: Version,
}

pub(super) fn merge(
    cx: &mut Cx,
    root: StatId,
    method: &StructMethod,
    owner: VarProcessorId,
) -> io::Result<()> {
    let mut arguments = Scope::default();
    let is_static = method.access_flags & ACC_STATIC != 0;
    if !is_static {
        arguments.insert(Some(0), Version::new(0, 0));
    }
    let descriptor = MethodDescriptor::parse_descriptor(&method.descriptor);
    for (slot, _) in descriptor.parameter_slots(is_static) {
        arguments.insert(Some(slot), Version::new(slot, 0));
    }

    let mut pass = Merge { cx, root, owner };
    pass.populate_type_bounds();
    let old_sources = pass
        .cx
        .options
        .verify_pre_post_merges
        .then(|| variable_sources(&mut pass.cx.ir, root, method))
        .flatten();

    let mut denylist = Denylist::default();
    while let Some(candidate) =
        pass.find_candidate(root, &arguments, &mut Scope::default(), &denylist)?
    {
        if !pass.remap_statement(root, candidate)? {
            denylist.insert(candidate.from, candidate.to);
        }
    }

    if let Some(old_sources) = old_sources
        && let Some(new_sources) = variable_sources(&mut pass.cx.ir, root, method)
    {
        pass.compare_sources(&old_sources, &new_sources)?;
    }
    Ok(())
}

struct Merge<'a> {
    cx: &'a mut Cx,
    root: StatId,
    owner: VarProcessorId,
}

impl Merge<'_> {
    fn populate_type_bounds(&mut self) {
        let mut statements = VecDeque::from([self.root]);
        while let Some(stat) = statements.pop_front() {
            if let Some(body) = self.cx.ir[stat].exprents {
                let mut expressions = VecDeque::from(self.cx.ir[body].clone());
                while let Some(expr) = expressions.pop_front() {
                    let (instance, target) = match &self.cx.ir[expr].kind {
                        ExprKind::Invocation(invoke) => (invoke.instance, invoke.classname.clone()),
                        ExprKind::Field(field) => (field.instance, field.classname.clone()),
                        ExprKind::Exit {
                            kind: ExitType::Return,
                            value,
                            return_type,
                            ..
                        } => (*value, return_type.as_ref().and_then(|ty| ty.value.clone())),
                        ExprKind::Exit { .. } => continue,
                        _ => {
                            expressions.extend(Expr::children(&self.cx.ir, expr));
                            continue;
                        }
                    };
                    if target.as_deref() == Some("java/lang/Object") {
                        continue;
                    }
                    if let Some(var) = instance.and_then(|id| Expr::variable(&self.cx.ir, id)) {
                        let pair = var.pair();
                        let mut ty = VarType::new(CodeType::Object);
                        ty.value = target;
                        let previous = self.cx.ir[self.owner]
                            .versions
                            .upper
                            .get(&pair)
                            .and_then(Option::as_ref);
                        if previous.is_none_or(|previous| {
                            &ty != previous
                                && (previous.ty != CodeType::Object
                                    || instance_of(self.cx, &ty, previous))
                        }) {
                            self.cx.ir[self.owner].versions.upper.insert(pair, Some(ty));
                        }
                    }
                }
            }
            statements.extend(self.cx.ir[stat].stats.iter().copied());
        }
    }

    fn original_slot(&self, index: i32) -> Option<i32> {
        self.cx.ir[self.owner]
            .versions
            .original
            .get(&index)
            .map(|pair| pair.var)
    }

    fn find_candidate(
        &mut self,
        stat: StatId,
        parent: &Scope,
        leaked: &mut Scope,
        denylist: &Denylist,
    ) -> io::Result<Option<Candidate>> {
        let mut active = parent.clone();
        for index in 0..self.cx.ir[stat].var_definitions.len() {
            let expr = self.cx.ir[stat].var_definitions[index];
            let Some(from) = Expr::variable(&self.cx.ir, expr).map(|var| var.pair()) else {
                continue;
            };
            let Some(slot) = self.original_slot(from.var) else {
                self.cx.ir[self.root]
                    .add_comment("$VF: One or more variable merging failures!", true);
                continue;
            };
            if let Some(to) = active.insert(Some(slot), from) {
                // Upstream removes this declaration before attempting the remap.
                self.cx.ir[stat].var_definitions.remove(index);
                return Ok(Some(Candidate { from, to }));
            }
            leaked.insert(Some(slot), from);
        }

        let leaks_expressions = matches!(
            self.cx.ir[stat].kind,
            StatementKind::BasicBlock { .. }
                | StatementKind::General { .. }
                | StatementKind::Root { .. }
                | StatementKind::Sequence
        );
        let body = self.cx.ir[stat].exprents;
        let headers;
        let expressions = if let Some(body) = body {
            self.cx.ir[body].as_slice()
        } else {
            headers = stat.stat_exprents(&self.cx.ir);
            &headers
        };

        for (index, &expr) in expressions.iter().enumerate() {
            let Some(candidate) = self.consider_definition(
                expr,
                &mut active,
                leaks_expressions.then_some(&mut *leaked),
                denylist,
            ) else {
                continue;
            };
            // A later read of the old variable permits a header merge and
            // prevents a merge from a basic block's expression list.
            if is_var_read_first(&self.cx.ir, candidate.to, stat, index + 1, &[]) != body.is_none()
            {
                continue;
            }
            if self.types_comparable(candidate)?
                && (body.is_none()
                    || !self.cx.options.verify_merges
                    || self.safe_body_merge(stat, expr, candidate))
            {
                return Ok(Some(candidate));
            }
        }

        if body.is_none() {
            for index in 0..self.cx.ir[stat].stats.len() {
                let child = self.cx.ir[stat].stats[index];
                let mut child_leaked = Scope::default();
                if let Some(candidate) =
                    self.find_candidate(child, &active, &mut child_leaked, denylist)?
                {
                    return Ok(Some(candidate));
                }
                let head = self.cx.ir[stat].first == Some(child);
                match &self.cx.ir[stat].kind {
                    StatementKind::If(branch) => {
                        if branch.if_stat == Some(child) || branch.else_stat == Some(child) {
                            continue;
                        }
                        if head {
                            leaked.extend(child_leaked.iter().map(|(slot, pair)| (*slot, *pair)));
                        }
                    }
                    StatementKind::Switch(_) | StatementKind::Synchronized { .. } => {
                        if !head {
                            continue;
                        }
                        leaked.extend(child_leaked.iter().map(|(slot, pair)| (*slot, *pair)));
                    }
                    StatementKind::Catch { .. } | StatementKind::CatchAll { .. } => continue,
                    _ => {}
                }
                active.extend(child_leaked);
            }
        }
        Ok(None)
    }

    fn consider_definition(
        &self,
        expr: ExprId,
        active: &mut Scope,
        leaked: Option<&mut Scope>,
        denylist: &Denylist,
    ) -> Option<Candidate> {
        let ir = &self.cx.ir;
        let lhs = ir[expr].as_assignment().map_or(expr, |(left, _)| left);
        let var = Expr::variable(ir, lhs).filter(|var| var.definition)?;
        let from = var.pair();
        let slot = self.original_slot(from.var);
        if let Some(&to) = active.get(&slot)
            && denylist.get(&from) != Some(&to)
        {
            return Some(Candidate { from, to });
        }
        active.insert(slot, from);
        if let Some(leaked) = leaked {
            leaked.insert(slot, from);
        }
        None
    }

    fn types_comparable(&self, candidate: Candidate) -> io::Result<bool> {
        let lower = &self.cx.ir[self.owner].versions.lower;
        let (Some(from), Some(to)) = (lower.get(&candidate.from), lower.get(&candidate.to)) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "Assertion failed: Var types not processed! Is the graph broken?",
            ));
        };
        Ok(from.higher_equal_in_lattice_than(self.cx, to)
            || to.higher_equal_in_lattice_than(self.cx, from))
    }

    fn safe_body_merge(&self, stat: StatId, expr: ExprId, candidate: Candidate) -> bool {
        let ir = &self.cx.ir;
        let Some((lhs, rhs)) = ir[expr].as_assignment() else {
            return true;
        };
        if Expr::variable(ir, lhs).is_none_or(|var| var.index != candidate.from.var) {
            return true;
        }
        let search = merge_parent(ir, stat);
        let check_assignment = !Expr::contains_var(ir, rhs, candidate.to);
        !is_var_read_remote(ir, search, candidate.from, check_assignment, stat)
    }

    fn remap_statement(&mut self, stat: StatId, candidate: Candidate) -> io::Result<bool> {
        let Candidate { from, to } = candidate;
        if from == to {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "Trying to remap var version {from} in statement {} to itself!",
                    self.cx.ir[stat].id
                ),
            ));
        }
        let mut success = false;
        if let Some(body) = self.cx.ir[stat].exprents {
            let mut index = 0;
            while index < self.cx.ir[body].len() {
                let expr = self.cx.ir[body][index];
                if self.remap_expression(expr, candidate) {
                    success = true;
                    if Expr::variable(&self.cx.ir, expr).is_some_and(|var| !var.definition) {
                        self.cx.ir[body].remove(index);
                        continue;
                    }
                }
                index += 1;
            }
        } else {
            for index in 0..self.cx.ir[stat].stats.len() {
                success |= self.remap_statement(self.cx.ir[stat].stats[index], candidate)?;
            }
            for expr in stat.stat_exprents(&self.cx.ir) {
                success |= self.remap_expression(expr, candidate);
            }
        }

        if success {
            let mut index = 0;
            while index < self.cx.ir[stat].var_definitions.len() {
                let expr = self.cx.ir[stat].var_definitions[index];
                if let Some(var) = Expr::variable(&self.cx.ir, expr) {
                    if var.pair() == from {
                        self.cx.ir[stat].var_definitions.remove(index);
                        continue;
                    }
                    if var.pair() == to
                        && let Some(merged) = self.merged_type(candidate)
                        && let ExprKind::Variable(var) = &mut self.cx.ir[expr].kind
                    {
                        var.var_type = Some(merged);
                    }
                }
                index += 1;
            }
        }
        Ok(success)
    }

    fn remap_expression(&mut self, tree: ExprId, candidate: Candidate) -> bool {
        let Candidate { from, to } = candidate;
        let mut success = false;
        for expr in Expr::all_exprents(&self.cx.ir, tree, true, true) {
            match &self.cx.ir[expr].kind {
                ExprKind::Assignment { left, right, .. } => {
                    let right = *right;
                    if Expr::variable(&self.cx.ir, *left)
                        .is_some_and(|var| var.pair() == from || var.pair() == to)
                        && let ExprKind::Constant { var_type, .. } = &self.cx.ir[right].kind
                        && var_type.ty != CodeType::Null
                        && let Some(merged) = self.merged_type(candidate)
                        && merged.higher_equal_in_lattice_than(self.cx, var_type)
                        && can_merge_constant(&merged)
                        && let ExprKind::Constant { var_type, .. } = &mut self.cx.ir[right].kind
                    {
                        *var_type = merged;
                    }
                }
                ExprKind::Variable(var) if var.pair() == from => {
                    let Some(merged) = self.merged_type(candidate) else {
                        continue;
                    };
                    let ExprKind::Variable(var) = &mut self.cx.ir[expr].kind else {
                        unreachable!();
                    };
                    var.index = to.var;
                    var.version = to.version;
                    var.var_type = Some(merged.clone());
                    var.definition = false;
                    self.cx.ir[self.owner].versions.lower.insert(to, merged);
                    success = true;
                }
                _ => {}
            }
        }
        success
    }

    fn merged_type(&self, candidate: Candidate) -> Option<VarType> {
        let types = &self.cx.ir[self.owner].versions;
        let from = types.lower.get(&candidate.from)?;
        let to = types.lower.get(&candidate.to)?;
        if from == to {
            return Some(from.clone());
        }
        let joined = VarType::join(self.cx, from, to)?;
        if joined.ty != CodeType::Object {
            return from.higher_in_lattice_than(self.cx, to).then_some(joined);
        }
        let from_max = types.upper.get(&candidate.from).and_then(Option::as_ref);
        let to_max = types.upper.get(&candidate.to).and_then(Option::as_ref);
        let (subtype, supertype) = match (from_max, to_max) {
            (Some(from_max), Some(to_max)) => (from_max, to_max),
            (None, Some(to_max)) => (from, to_max),
            (Some(from_max), None) => (from_max, to),
            (None, None) => {
                return (instance_of(self.cx, to, from) || instance_of(self.cx, from, to))
                    .then(|| to.clone());
            }
        };
        instance_of(self.cx, subtype, supertype).then(|| subtype.clone())
    }

    fn compare_sources(&mut self, old: &Sources, new: &Sources) -> io::Result<()> {
        // Java's diagnostics iterate identity-hashed objects. Graph allocation
        // order gives the same checks stable ordering here.
        for (&expr, sources) in old {
            if new.get(&expr) != Some(sources) {
                let var = diagnostic_variable(self.cx, expr)?;
                self.cx.ir[self.root].add_comment(
                    &format!("$VF: Variable merging failed for merge {var}. Code has semantic differences!"),
                    false,
                );
            }
        }
        for &expr in new.keys() {
            if !old.contains_key(&expr) {
                let var = diagnostic_variable(self.cx, expr)?;
                self.cx.ir[self.root]
                    .add_comment(&format!("$VF: Variable merging added a var? {var}"), false);
            }
        }
        Ok(())
    }
}

fn instance_of(cx: &Cx, subclass: &VarType, superclass: &VarType) -> bool {
    match (subclass.value.as_deref(), superclass.value.as_deref()) {
        (Some(subclass), Some(superclass)) => cx.classes().instance_of(subclass, superclass),
        _ => false,
    }
}

fn can_merge_constant(ty: &VarType) -> bool {
    if ty.type_family != TypeFamily::Object || ty.ty == CodeType::Null {
        return true;
    }
    // These two singletons retain their static class-name ArcStr on clone.
    [VarType::VARTYPE_STRING, VarType::VARTYPE_CLASS]
        .iter()
        .any(|constant| {
            ty == constant
                && ArcStr::ptr_eq(ty.value.as_ref().unwrap(), constant.value.as_ref().unwrap())
        })
}

fn write_operand(ir: &Ir, expr: ExprId) -> Option<ExprId> {
    match &ir[expr].kind {
        ExprKind::Assignment { left, .. } => Some(*left),
        ExprKind::Function { op, operands, .. } if op.is_inc_dec() => Some(operands[0]),
        _ => None,
    }
}

pub(super) fn is_var_read_first(
    ir: &Ir,
    var: Version,
    stat: StatId,
    index: usize,
    allowlist: &[ExprId],
) -> bool {
    let read = |expr| {
        let written = write_operand(ir, expr);
        Expr::all_exprents(ir, expr, true, true)
            .into_iter()
            .any(|expr| {
                Some(expr) != written
                    && !allowlist.contains(&expr)
                    && Expr::variable(ir, expr).is_some_and(|other| other.pair() == var)
            })
    };
    if let Some(body) = ir[stat].exprents {
        return ir[body].iter().copied().skip(index).any(read);
    }
    let headers = stat.stat_exprents(ir);
    let first_child = index.saturating_sub(headers.len());
    headers.into_iter().skip(index).any(read)
        || ir[stat]
            .stats
            .iter()
            .skip(first_child)
            .any(|&child| is_var_read_first(ir, var, child, 0, allowlist))
}

fn merge_parent(ir: &Ir, stat: StatId) -> StatId {
    let parent = ir[stat].parent.expect("Missing parent of assignment");
    if matches!(
        ir[parent].kind,
        StatementKind::If(_) | StatementKind::Switch(_)
    ) {
        let mut head = parent;
        while !matches!(ir[head].kind, StatementKind::BasicBlock { .. }) {
            head = ir[head].first.expect("Missing basic head");
        }
        if head == stat {
            return ir[parent]
                .parent
                .expect("Missing parent of assignment head");
        }
    }
    parent
}

fn is_var_read_remote(
    ir: &Ir,
    stat: StatId,
    var: Version,
    check_assignment: bool,
    skip: StatId,
) -> bool {
    if ir[stat]
        .stats
        .iter()
        .any(|&child| is_var_read_remote(ir, child, var, check_assignment, skip))
    {
        return true;
    }
    if stat == skip || !matches!(ir[stat].kind, StatementKind::BasicBlock { .. }) {
        return false;
    }
    let body = ir[stat].exprents.expect("Missing basic block body");
    ir[body].iter().copied().any(|expr| {
        if check_assignment {
            Expr::all_exprents(ir, expr, true, true)
                .into_iter()
                .any(|expr| {
                    write_operand(ir, expr)
                        .and_then(|operand| Expr::variable(ir, operand))
                        .is_some_and(|other| other.index == var.var)
                })
        } else {
            Expr::contains_var(ir, expr, var)
        }
    })
}

fn variable_sources(ir: &mut Ir, root: StatId, method: &StructMethod) -> Option<Sources> {
    let Ok(result) = try_split_ssau(ir, root, method) else {
        reset_versions(ir, root);
        return None;
    };
    let versions = result.versions;
    let mut lookup = FxHashMap::default();
    collect_variables(ir, root, &mut lookup);
    let mut sources = Sources::default();
    for node in &versions.graph.nodes {
        if let Some(&target) = lookup.get(&node.as_pair()) {
            let predecessors: FxHashSet<_> = node
                .predecessors
                .iter()
                .copied()
                .chain(node.phantom_node)
                .filter_map(|pair| lookup.get(&pair).copied())
                .collect();
            if !predecessors.is_empty() {
                sources.insert(target, predecessors);
            }
        }
    }
    reset_versions(ir, root);
    Some(sources)
}

fn collect_variables(ir: &Ir, stat: StatId, lookup: &mut FxHashMap<Version, ExprId>) {
    for &expr in &ir[stat].var_definitions {
        if let Some(var) = Expr::variable(ir, expr) {
            lookup.insert(var.pair(), expr);
        }
    }
    if let Some(body) = ir[stat].exprents {
        for &expr in &ir[body] {
            for expr in Expr::all_exprents(ir, expr, true, true) {
                if let Some(var) = Expr::variable(ir, expr) {
                    lookup.insert(var.pair(), expr);
                }
            }
        }
    }
    for &child in ir[stat].stats.iter() {
        collect_variables(ir, child, lookup);
    }
}

fn diagnostic_variable(cx: &mut Cx, expr: ExprId) -> io::Result<String> {
    let var = Expr::variable(&cx.ir, expr).expect("Expected a variable");
    let pair = var.pair();
    let definition = if var.definition { " Def" } else { "" };
    let rendered =
        cx.with_locked_imports(|cx| crate::decompiler::exps::write::to_java(cx, expr, 0))?;
    let source = rendered.convert_to_string_and_allow_data_discard();
    Ok(format!(
        "VarExprent[{},{version}{definition}]: {{{source}}}",
        pair.var,
        version = pair.version
    ))
}
