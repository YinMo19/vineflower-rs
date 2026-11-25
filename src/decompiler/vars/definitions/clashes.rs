// Copyright 2000-2024 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Lexical name resolution for declarations, flow-scoped patterns and nested methods.

use std::io;
use std::sync::Arc;

use arcstr::ArcStr;
use rustc_hash::{FxHashMap, FxHashSet};

use crate::code::code_constants::{ACC_STATIC, ACC_SYNTHETIC};
use crate::decompiler::exps::{Expr, ExprKind, FunctionType};
use crate::decompiler::ir::{ExprId, StatId, VarProcessorId};
use crate::decompiler::stats::{LoopType, StatementKind, stat_edge::EdgeType};
use crate::decompiler::vars::var_version_pair::VarVersionPair;
use crate::engine::Cx;
use crate::engine::class_wrapper::MethodWrapper;
use crate::structs::{StructMember, StructMethod};
use crate::types::MethodDescriptor;
use crate::util::interpreter_util::make_unique_key;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Definition {
    method: VarProcessorId,
    pair: VarVersionPair,
}

type Definitions = FxHashSet<Definition>;
type Renames = FxHashMap<VarVersionPair, ArcStr>;

struct MethodNames {
    variables: VarProcessorId,
    renames: Renames,
}

impl MethodNames {
    fn definition(&self, pair: VarVersionPair) -> Definition {
        Definition {
            method: self.variables,
            pair,
        }
    }
}

struct Scopes<'a> {
    cx: &'a mut Cx,
    // Definitions printed ahead of a statement belong to its parent's scope.
    statements: FxHashMap<Option<StatId>, Definitions>,
    live: Definitions,
    names: FxHashMap<Definition, Option<ArcStr>>,
    // Java uses method keys for recursion control and method identity for bindings.
    seen: FxHashSet<String>,
}

/// `VarDefinitionHelper.remapClashingNames`. Return changes for this method;
/// names in published nested methods are applied during the traversal.
pub(crate) fn remap_clashing_names(
    cx: &mut Cx,
    root: StatId,
    method: &StructMethod,
    variables: VarProcessorId,
) -> io::Result<Renames> {
    let mut scopes = Scopes {
        cx,
        statements: FxHashMap::default(),
        live: Definitions::default(),
        names: FxHashMap::default(),
        seen: FxHashSet::default(),
    };
    let mut current = MethodNames {
        variables,
        renames: Renames::default(),
    };
    let descriptor = MethodDescriptor::parse_descriptor(&method.descriptor);
    for (slot, _) in descriptor.parameter_slots(method.has_modifier(ACC_STATIC)) {
        let pair = VarVersionPair::new(slot, 0);
        let definition = current.definition(pair);
        scopes.live.insert(definition);
        scopes
            .names
            .insert(definition, scopes.method_name(variables, pair));
    }

    scopes
        .seen
        .insert(make_unique_key(&method.name, &method.descriptor));
    scopes.statement(root, &mut current)?;
    Ok(current.renames)
}

impl Scopes<'_> {
    fn statement(&mut self, stat: StatId, method: &mut MethodNames) -> io::Result<()> {
        let parent = self.cx.ir[stat].parent;
        for expr in self.cx.ir[stat].var_definitions.clone() {
            let mut preceding = Definitions::default();
            self.plain_expr(stat, method, expr, &mut preceding)?;
            self.live.extend(&preceding);
            self.statements.entry(parent).or_default().extend(preceding);
        }

        // The basic head of an if is printed before its condition and branches.
        let if_head = matches!(self.cx.ir[stat].kind, StatementKind::If(_))
            .then(|| stat.get_basic_head(&self.cx.ir));
        if let Some(head) = if_head {
            let mut preceding = Definitions::default();
            for expr in self.cx.ir[self.cx.ir[head].exprents.unwrap()].clone() {
                self.plain_expr(head, method, expr, &mut preceding)?;
            }
            self.live.extend(&preceding);
            self.statements.entry(parent).or_default().extend(preceding);
        }

        let expressions = self.cx.ir[stat].exprents;
        let mut current = Definitions::default();
        let mut entering = FxHashMap::default();
        let mut after = Definitions::default();
        if let Some(list) = expressions {
            for expr in self.cx.ir[list].clone() {
                self.plain_expr(stat, method, expr, &mut current)?;
            }
        } else {
            self.statement_head(stat, method, &mut current, &mut entering, &mut after)?;
        }
        self.live.extend(&current);
        self.statements.insert(Some(stat), current);

        let separate = matches!(
            self.cx.ir[stat].kind,
            StatementKind::If(_) | StatementKind::Catch { .. }
        );
        if !matches!(self.cx.ir[stat].kind, StatementKind::Switch(_)) || !self.cx.ir[stat].phantom {
            let children: Vec<_> = self.cx.ir[stat].stats.iter().copied().collect();
            for child in children {
                if Some(child) == if_head {
                    continue;
                }
                let in_child = entering.remove(&child).unwrap_or_default();
                self.live.extend(&in_child);
                self.statement(child, method)?;
                self.remove_live(&in_child);
                if separate {
                    self.clear_statement(child);
                    self.clear_statement(stat);
                }
            }
        }

        if expressions.is_none() {
            self.clear_statement(stat);
        }
        if self.statements.contains_key(&None) {
            return Err(io::Error::other(
                "Variable definition has no owning statement",
            ));
        }
        let children: Vec<_> = self
            .statements
            .keys()
            .flatten()
            .copied()
            .filter(|&child| self.cx.ir[child].parent == Some(stat))
            .collect();
        for child in children {
            self.clear_statement(child);
        }

        if !matches!(self.cx.ir[stat].kind, StatementKind::Root { .. }) {
            self.live.extend(&after);
            self.statements.entry(parent).or_default().extend(after);
        }
        Ok(())
    }

    fn statement_head(
        &mut self,
        stat: StatId,
        method: &mut MethodNames,
        current: &mut Definitions,
        entering: &mut FxHashMap<StatId, Definitions>,
        after: &mut Definitions,
    ) -> io::Result<()> {
        match &self.cx.ir[stat].kind {
            StatementKind::Catch {
                vars, resources, ..
            } => {
                let children: Vec<_> = self.cx.ir[stat].stats.iter().copied().collect();
                let resources = resources.map_or_else(Vec::new, |list| self.cx.ir[list].clone());
                let vars = vars.clone();
                for (index, child) in children.into_iter().enumerate() {
                    let mut definitions = Definitions::default();
                    let exprs = if index == 0 {
                        &resources[..]
                    } else {
                        &vars[index - 1..index]
                    };
                    for &expr in exprs {
                        self.plain_expr(child, method, expr, &mut definitions)?;
                    }
                    self.remove_live(&definitions);
                    entering.insert(child, definitions);
                }
            }
            StatementKind::Switch(switch) => {
                let head = self.cx.ir[switch.head_exprents.unwrap()][0];
                let labels: Vec<_> = switch
                    .cases
                    .iter()
                    .enumerate()
                    .map(|(index, case)| {
                        let guard = switch.case_guards.get(index).copied().flatten();
                        (case.statement, case.values.clone(), guard)
                    })
                    .collect();
                self.plain_expr(stat, method, head, current)?;
                for (child, values, guard) in labels {
                    let mut definitions = Definitions::default();
                    for expr in values.into_iter().flatten().chain(guard) {
                        self.plain_expr(child, method, expr, &mut definitions)?;
                    }
                    self.remove_live(&definitions);
                    entering.insert(child, definitions);
                }
            }
            StatementKind::If(branch) => {
                let head = self.cx.ir[branch.head_exprents.unwrap()][0];
                let ExprKind::If { condition } = self.cx.ir[head].kind else {
                    unreachable!("If header must be an IfExprent");
                };
                let (then_branch, else_branch) = (branch.if_stat, branch.else_stat);
                let mut when_true = Definitions::default();
                let mut when_false = Definitions::default();
                self.expr(
                    stat,
                    method,
                    condition,
                    current,
                    &mut when_true,
                    &mut when_false,
                )?;
                let completes_normally = |child: Option<StatId>| {
                    child.is_none_or(|child| {
                        !child
                            .get_successor_edges(&self.cx.ir, EdgeType::Regular.mask())
                            .is_empty()
                    })
                };
                match (
                    completes_normally(then_branch),
                    completes_normally(else_branch),
                ) {
                    (false, true) => after.extend(&when_false),
                    (true, false) => after.extend(&when_true),
                    _ => {}
                }
                entering.extend(then_branch.map(|branch| (branch, when_true)));
                entering.extend(else_branch.map(|branch| (branch, when_false)));
            }
            StatementKind::Do(header) => {
                let header = *header;
                let mut when_true = Definitions::default();
                let mut when_false = Definitions::default();
                if let Some(init) = header.init(&self.cx.ir) {
                    self.plain_expr(stat, method, init, current)?;
                }
                if let Some(condition) = header.condition(&self.cx.ir) {
                    self.expr(
                        stat,
                        method,
                        condition,
                        current,
                        &mut when_true,
                        &mut when_false,
                    )?;
                }
                if let Some(increment) = header.increment(&self.cx.ir) {
                    self.live.extend(&when_true);
                    self.plain_expr(stat, method, increment, current)?;
                    self.remove_live(&when_true);
                }
                if matches!(header.ty, LoopType::While | LoopType::For) {
                    entering.insert(self.cx.ir[stat].first.unwrap(), when_true);
                }
                if stat
                    .get_successor_edges(&self.cx.ir, EdgeType::Break.mask())
                    .is_empty()
                {
                    *after = when_false;
                }
            }
            _ => {
                for expr in stat.stat_exprents(&self.cx.ir) {
                    self.plain_expr(stat, method, expr, current)?;
                }
            }
        }

        Ok(())
    }

    fn clear_statement(&mut self, stat: StatId) {
        if let Some(definitions) = self.statements.remove(&Some(stat)) {
            for definition in definitions {
                self.live.remove(&definition);
                self.names.remove(&definition);
            }
        }
    }

    fn remove_live(&mut self, definitions: &Definitions) {
        for definition in definitions {
            self.live.remove(definition);
        }
    }

    fn plain_expr(
        &mut self,
        stat: StatId,
        method: &mut MethodNames,
        expr: ExprId,
        current: &mut Definitions,
    ) -> io::Result<()> {
        self.expr(
            stat,
            method,
            expr,
            current,
            &mut Definitions::default(),
            &mut Definitions::default(),
        )
    }

    fn expr(
        &mut self,
        stat: StatId,
        method: &mut MethodNames,
        expr: ExprId,
        current: &mut Definitions,
        when_true: &mut Definitions,
        when_false: &mut Definitions,
    ) -> io::Result<()> {
        match &self.cx.ir[expr].kind {
            ExprKind::New {
                new_type,
                lambda,
                anonymous,
                method_reference,
                ..
            } if (*lambda && !method_reference) || (!lambda && *anonymous) => {
                if let Some(owner) = new_type.value.clone() {
                    self.nested_methods(&owner, *lambda)?;
                }
            }
            ExprKind::Variable(var) if var.definition => {
                let pair = var.pair();
                let definition = method.definition(pair);
                current.insert(definition);
                self.live.insert(definition);
                let name = var
                    .lvt
                    .as_ref()
                    .map(|lvt| lvt.get_name().clone())
                    .or_else(|| self.method_name(method.variables, pair));
                if let Some(original) = name {
                    let mut name = self.rename(original.clone());
                    if name != original {
                        if self.scope_case(stat, &original)? {
                            name = original;
                        } else {
                            method.renames.insert(pair, name.clone());
                        }
                    }
                    self.names.insert(definition, Some(name));
                }
            }
            ExprKind::Function { op, operands, .. } => match op {
                FunctionType::BoolAnd => {
                    for operand in operands.clone() {
                        self.live.extend(&*when_true);
                        self.expr(
                            stat,
                            method,
                            operand,
                            current,
                            when_true,
                            &mut Definitions::default(),
                        )?;
                    }
                    self.remove_live(when_true);
                    return Ok(());
                }
                FunctionType::BoolOr => {
                    for operand in operands.clone() {
                        self.live.extend(&*when_false);
                        self.expr(
                            stat,
                            method,
                            operand,
                            current,
                            &mut Definitions::default(),
                            when_false,
                        )?;
                    }
                    self.remove_live(when_false);
                    return Ok(());
                }
                FunctionType::BoolNot => {
                    return self.expr(stat, method, operands[0], current, when_false, when_true);
                }
                FunctionType::Ternary => {
                    let [condition, consequent, alternative] = operands[..] else {
                        unreachable!("Ternary must have three operands");
                    };
                    let mut true_branch = Definitions::default();
                    let mut false_branch = Definitions::default();
                    self.expr(
                        stat,
                        method,
                        condition,
                        current,
                        &mut true_branch,
                        &mut false_branch,
                    )?;
                    self.live.extend(&true_branch);
                    self.plain_expr(stat, method, consequent, current)?;
                    self.remove_live(&true_branch);
                    self.live.extend(&false_branch);
                    self.plain_expr(stat, method, alternative, current)?;
                    self.remove_live(&false_branch);
                    return Ok(());
                }
                FunctionType::InstanceOf if operands.len() > 2 => {
                    let (value, pattern) = (operands[0], operands[2]);
                    self.plain_expr(stat, method, value, current)?;
                    self.plain_expr(stat, method, pattern, when_true)?;
                    self.remove_live(when_true);
                    return Ok(());
                }
                _ => {}
            },
            _ => {}
        }

        let children: Vec<_> = Expr::children(&self.cx.ir, expr).collect();
        for child in children {
            self.plain_expr(stat, method, child, current)?;
        }
        Ok(())
    }

    fn method_name(&self, method: VarProcessorId, pair: VarVersionPair) -> Option<ArcStr> {
        self.cx.ir[method].names.get(&pair).cloned().flatten()
    }

    fn rename(&self, mut name: ArcStr) -> ArcStr {
        while self
            .live
            .iter()
            .any(|def| self.names.get(def).and_then(Option::as_ref) == Some(&name))
        {
            name = format!("{name}x").into();
        }
        name
    }

    fn scope_case(&mut self, stat: StatId, name: &str) -> io::Result<bool> {
        let mut parent = self.cx.ir[stat].parent;
        while let Some(candidate) = parent {
            let owner = &self.cx.ir[candidate];
            if matches!(owner.kind, StatementKind::Sequence)
                || (matches!(owner.kind, StatementKind::If(_)) && owner.first == Some(stat))
            {
                parent = owner.parent;
            } else {
                break;
            }
        }
        let Some(parent) = parent else {
            return Ok(false);
        };
        let StatementKind::Switch(switch) = &self.cx.ir[parent].kind else {
            return Ok(false);
        };

        let mut matching = Definitions::default();
        for (&def, entry) in &self.names {
            let entry = entry
                .as_deref()
                .ok_or_else(|| io::Error::other("Null name in switch clash scope"))?;
            if entry == name {
                matching.insert(def);
            }
        }

        let mut cases: Vec<_> = switch
            .cases
            .iter()
            .map(|case| case.statement)
            .filter(|&case| {
                self.statements
                    .get(&Some(case))
                    .is_some_and(|defs| !defs.is_disjoint(&matching))
            })
            .collect();
        if cases.is_empty() {
            return Ok(false);
        }
        if let Some(owning_case) = switch
            .cases
            .iter()
            .map(|case| case.statement)
            .find(|&case| case == stat || case.contains_statement_strict(&self.cx.ir, stat))
        {
            cases.push(owning_case);
        }
        let StatementKind::Switch(switch) = &mut self.cx.ir[parent].kind else {
            unreachable!()
        };
        switch.scoped_case_statements.extend(cases);
        Ok(true)
    }

    fn nested_methods(&mut self, owner: &str, lambda: bool) -> io::Result<()> {
        let Some(node) = self.cx.class_nodes.id(owner) else {
            return Ok(());
        };
        let Some(owner) = self.cx.class_nodes.wrapper_owner(node) else {
            return Ok(());
        };
        let class = &self.cx.class_nodes[owner];
        let Some(wrapper) = &class.wrapper else {
            return Ok(());
        };

        if lambda {
            let info = self.cx.class_nodes[node]
                .lambda
                .as_ref()
                .ok_or_else(|| io::Error::other("Lambda allocation has no class node metadata"))?;
            let Some(index) = class
                .class
                .methods
                .index_of_key(info.content_method_key.as_str())
            else {
                return Ok(());
            };
            let target = NestedMethod::from(&wrapper.methods[index]);
            let descriptor = MethodDescriptor::parse_descriptor(&info.content_method_descriptor);
            let sam = MethodDescriptor::parse_descriptor(&info.method_descriptor);
            let skip = descriptor.params.len().saturating_sub(sam.params.len());
            self.nested_method(
                target,
                &descriptor,
                info.is_content_method_static,
                skip,
                lambda,
            )?;
        } else {
            let targets: Vec<_> = wrapper
                .methods
                .iter()
                .filter(|method| !method.method.has_modifier(ACC_SYNTHETIC))
                .map(NestedMethod::from)
                .collect();
            for target in targets {
                let descriptor = MethodDescriptor::parse_descriptor(&target.method.descriptor);
                let is_static = target.method.has_modifier(ACC_STATIC);
                self.nested_method(
                    target,
                    &descriptor,
                    is_static,
                    usize::from(!is_static),
                    lambda,
                )?;
            }
        }
        Ok(())
    }

    fn nested_method(
        &mut self,
        target: NestedMethod,
        descriptor: &MethodDescriptor,
        is_static: bool,
        skip: usize,
        lambda: bool,
    ) -> io::Result<()> {
        if !self.seen.insert(make_unique_key(
            &target.method.name,
            &target.method.descriptor,
        )) {
            return Ok(());
        }

        let mut method = MethodNames {
            variables: target.variables,
            renames: Renames::default(),
        };
        for (slot, _) in descriptor.parameter_slots(is_static).skip(skip) {
            let pair = VarVersionPair::new(slot, 0);
            let Some(original) = self.method_name(target.variables, pair) else {
                if lambda {
                    return Err(io::Error::other(
                        "Null parameter name in lambda clash scope",
                    ));
                }
                continue;
            };
            let name = self.rename(original.clone());
            if name != original {
                self.cx.ir[target.variables]
                    .clashing_names
                    .insert(pair, name.clone());
                self.names.insert(method.definition(pair), Some(name));
            }
        }

        let root = target
            .root
            .ok_or_else(|| io::Error::other("Nested method has no statement root"))?;
        self.statement(root, &mut method)?;
        self.cx.ir[target.variables]
            .clashing_names
            .extend(method.renames);
        self.names
            .retain(|definition, _| definition.method != target.variables);
        Ok(())
    }
}

struct NestedMethod {
    method: Arc<StructMethod>,
    variables: VarProcessorId,
    root: Option<StatId>,
}

impl From<&MethodWrapper> for NestedMethod {
    fn from(wrapper: &MethodWrapper) -> Self {
        Self {
            method: Arc::clone(&wrapper.method),
            variables: wrapper.variables,
            root: wrapper
                .body
                .as_ref()
                .ok()
                .and_then(Option::as_ref)
                .map(|body| body.root),
        }
    }
}
