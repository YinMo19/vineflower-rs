// Copyright 2000-2025 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Recover record deconstruction from component accessor try statements.

use std::io;
use std::sync::Arc;

use indexmap::IndexMap;
use rustc_hash::FxBuildHasher;

use crate::decompiler::exps::{ConstantValue, ExitType, Expr, ExprKind, FunctionType};
use crate::decompiler::ir::{EdgeId, ExprId, Ir, StatId};
use crate::decompiler::stats::stat_edge::EdgeType;
use crate::decompiler::stats::{IfStatement, Statement, StatementKind};
use crate::engine::{Cx, counter_container::CounterContainer};
use crate::structs::{StructClass, StructRecordComponent};
use crate::types::{CodeType, VarType};

pub(super) fn match_if(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    stat: StatId,
    branch: StatId,
    instance_of: ExprId,
    head: ExprId,
) -> io::Result<bool> {
    let ir = &cx.ir;
    let root = std::iter::successors(Some(stat), |&parent| ir[parent].parent)
        .last()
        .unwrap();
    if !root
        .method(ir)
        .bytecode_version
        .has_record_pattern_matching()
    {
        return Ok(false);
    }

    let ExprKind::Assignment { right: store, .. } = ir[head].kind else {
        unreachable!("Record pattern head must be an assignment");
    };
    let operands = instance_of_operands(ir, instance_of);
    let source = operands.get(2).copied().unwrap_or(operands[0]);
    if !Expr::equals(cx, source, store) {
        return Ok(false);
    }
    let ty = Expr::expr_type(cx, operands[1]);
    let Some(pattern) = identify(cx, counters, stat, branch, store, ty, false)? else {
        return Ok(false);
    };
    let ExprKind::Function { operands, .. } = &mut cx.ir[instance_of].kind else {
        unreachable!();
    };
    if let Some(binding) = operands.get_mut(2) {
        *binding = pattern;
    } else {
        operands.push(pattern);
    }
    let StatementKind::If(branch) = &mut cx.ir[stat].kind else {
        unreachable!();
    };
    branch.pattern_matched = true;
    Ok(true)
}

/// `IfPatternMatchProcessor.identifyRecordPatternMatch`.
pub(crate) fn identify(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    parent: StatId,
    branch: StatId,
    store: ExprId,
    ty: VarType,
    simulate: bool,
) -> io::Result<Option<ExprId>> {
    let Some(class) = record_class(cx, &ty) else {
        return Ok(None);
    };
    if class.get_record_components().is_none_or(<[_]>::is_empty) {
        return Ok(None);
    }

    let mut edits = Edits::default();
    let candidate = Record { class, store, ty };
    let Some(result) = candidate.scan(cx, counters, branch, 1, &mut edits)? else {
        return Ok(None);
    };
    if !simulate {
        if result.stat != branch {
            parent.replace_statement(&mut cx.ir, branch, result.stat);
            for edge in result
                .stat
                .get_successor_edges(&cx.ir, EdgeType::Break.mask())
            {
                edge.change_closure(&mut cx.ir, Some(parent));
            }
        }
        edits.apply(cx, counters);
    }
    Ok(Some(result.expr))
}

#[derive(Default)]
struct Edits {
    destroy: Vec<StatId>,
    // Java hashes these blocks by JVM identity. Visit them in discovery order.
    remove_exprs: IndexMap<StatId, Vec<ExprId>, FxBuildHasher>,
    remove_edges: Vec<EdgeId>,
}

impl Edits {
    fn apply(self, cx: &mut Cx, counters: &mut CounterContainer) {
        for stat in self.destroy {
            let replacement = Statement::new_empty_basic_block(&mut cx.ir, counters);
            stat.replace_with(&mut cx.ir, replacement);
        }
        for (stat, removed) in self.remove_exprs {
            let list = cx.ir[stat]
                .exprents
                .expect("Record pattern block has no expressions");
            let mut exprs = std::mem::take(&mut cx.ir[list]);
            exprs.retain(|&expr| !removed.iter().any(|&remove| Expr::equals(cx, expr, remove)));
            cx.ir[list] = exprs;
        }
        for edge in self.remove_edges {
            edge.remove(&mut cx.ir);
        }
    }

    fn collect_edges(&mut self, ir: &Ir, branch: StatId, original: StatId) {
        let breaks = EdgeType::Break.mask();
        for &stat in &self.destroy {
            match ir[stat].kind {
                StatementKind::Catch { .. } => {
                    for &child in &ir[stat].stats[..2] {
                        self.remove_edges
                            .extend(child.get_successor_edges(ir, breaks));
                    }
                }
                StatementKind::If(_) => {
                    self.remove_edges
                        .extend(stat.get_successor_edges(ir, breaks));
                }
                _ => {}
            }
        }
        if branch != original
            && let Some(parent) = ir[branch].parent
            && matches!(ir[parent].kind, StatementKind::If(_))
        {
            self.remove_edges
                .extend(parent.get_successor_edges(ir, breaks));
            let head = ir[parent].first.expect("If statement has no head");
            self.remove_edges
                .extend(head.get_successor_edges(ir, EdgeType::Regular.mask()));
        }
    }
}

struct Record {
    class: Arc<StructClass>,
    store: ExprId,
    ty: VarType,
}

struct PatternResult {
    expr: ExprId,
    stat: StatId,
    index: usize,
}

impl Record {
    /// `getChildPattern` tracks the current statement position through nested
    /// type refinements and collects edits for a successfully matched pattern.
    fn scan(
        self,
        cx: &mut Cx,
        counters: &mut CounterContainer,
        mut branch: StatId,
        mut index: usize,
        edits: &mut Edits,
    ) -> io::Result<Option<PatternResult>> {
        let Some(components) = self.class.get_record_components() else {
            return Ok(None);
        };
        let original = branch;
        let mut bindings = vec![None; components.len()];
        let mut nested = Vec::new();
        for (component, definition) in components.iter().enumerate() {
            let Some(&next) = cx.ir[branch].stats.get(index) else {
                return Ok(None);
            };
            let Some(found) = accessor_destination(cx, next, &self.ty, definition) else {
                return Ok(None);
            };
            edits.destroy.push(next);
            index += 1;

            if let Some(&next) = cx.ir[branch].stats.get(index) {
                let head = next.get_basic_head(&cx.ir);
                let list = cx.ir[head]
                    .exprents
                    .expect("Record pattern block has no expressions");
                let mut binding = None;
                if cx.ir[list].len() >= 2 {
                    binding = self.match_stack_moves(cx, branch, head, found, edits);
                } else if let Some(refinement) = match_refinement(cx, branch, next, index, edits)? {
                    edits.destroy.push(next);
                    binding = refinement.binding;
                    if let Some(definition) = refinement.nested {
                        nested.push((component, definition));
                    }
                    if refinement.inverted {
                        index += 1;
                    } else {
                        branch = refinement.body.ok_or_else(|| {
                            io::Error::new(
                                io::ErrorKind::InvalidData,
                                "Record type refinement has no body",
                            )
                        })?;
                        index = 0;
                    }
                }
                bindings[component] = Some(binding.unwrap_or(found));
                index += 1;
            }
        }

        edits.collect_edges(&cx.ir, branch, original);
        for (component, record) in nested {
            let mut additional = Edits::default();
            if let Some(pattern) = record.scan(cx, counters, branch, index, &mut additional)? {
                bindings[component] = Some(pattern.expr);
                branch = pattern.stat;
                index = pattern.index;
                edits.destroy.extend(additional.destroy);
                // Java putAll replaces expression-removal lists for shared blocks.
                edits.remove_exprs.extend(additional.remove_exprs);
                edits.remove_edges.extend(additional.remove_edges);
            }
        }

        let expr = Expr::record_pattern(
            &mut cx.ir,
            counters,
            self.class,
            self.ty,
            bindings.into_iter().flatten().collect(),
        );
        Ok(Some(PatternResult {
            expr,
            stat: branch,
            index,
        }))
    }

    fn match_stack_moves(
        &self,
        cx: &mut Cx,
        branch: StatId,
        head: StatId,
        found: ExprId,
        edits: &mut Edits,
    ) -> Option<ExprId> {
        let ir = &cx.ir;
        let list = ir[head]
            .exprents
            .expect("Record stack block has no expressions");
        let exprs = &ir[list];
        let [ex_assign, real_assign] = [exprs[0], exprs[1]];
        let (ex_var, initial) = ir[ex_assign].as_assignment()?;
        Expr::variable(ir, ex_var)?;
        if !Expr::equals(cx, initial, found) {
            return None;
        }
        let (real_var, source) = ir[real_assign].as_assignment()?;
        Expr::variable(ir, real_var)?;
        if !Expr::equals(cx, ex_var, source)
            || Expr::is_var_referenced_in_stat(ir, ex_var, branch, &[source])
        {
            return None;
        }
        if exprs.len() == 3
            && let Some((_, third)) = ir[exprs[2]].as_assignment()
            && Expr::equals(cx, third, self.store)
        {
            edits.destroy.push(head);
            // These breaks are removed eagerly, even during a speculative match.
            for edge in head.get_successor_edges(ir, EdgeType::Break.mask()) {
                edge.remove(&mut cx.ir);
            }
        } else {
            edits
                .remove_exprs
                .entry(head)
                .or_default()
                .extend([ex_assign, real_assign]);
        }
        Some(real_var)
    }
}

fn accessor_destination(
    cx: &Cx,
    stat: StatId,
    ty: &VarType,
    component: &StructRecordComponent,
) -> Option<ExprId> {
    let ir = &cx.ir;
    let StatementKind::Catch { vars, .. } = &ir[stat].kind else {
        return None;
    };
    let [entry] = vars.as_slice() else {
        return None;
    };
    if Expr::expr_type(cx, *entry).value.as_deref() != Some("java/lang/Throwable") {
        return None;
    }
    let [body, handler] = &ir[stat].stats[..] else {
        return None;
    };
    if !is_statement_match_throw(ir, *handler) {
        return None;
    }
    let expr = single_basic_expr(ir, *body)?;
    let (left, right) = ir[expr].as_assignment()?;
    if !Expr::variable(ir, left)?.stack {
        return None;
    }
    let ExprKind::Invocation(invoke) = &ir[right].kind else {
        return None;
    };
    (invoke.classname == ty.value && invoke.name == component.name).then_some(left)
}

/// An accessor failure propagates as `throw new MatchException(...)`.
pub(crate) fn is_statement_match_throw(ir: &Ir, stat: StatId) -> bool {
    let Some(expr) = single_basic_expr(ir, stat) else {
        return false;
    };
    let ExprKind::Exit {
        kind: ExitType::Throw,
        value: Some(value),
        ..
    } = ir[expr].kind
    else {
        return false;
    };
    matches!(&ir[value].kind, ExprKind::New { new_type, .. }
        if new_type.value.as_deref() == Some("java/lang/MatchException"))
}

struct Refinement {
    body: Option<StatId>,
    inverted: bool,
    binding: Option<ExprId>,
    nested: Option<Record>,
}

fn match_refinement(
    cx: &Cx,
    branch: StatId,
    next: StatId,
    index: usize,
    edits: &mut Edits,
) -> io::Result<Option<Refinement>> {
    let ir = &cx.ir;
    let StatementKind::If(if_statement) = ir[next].kind else {
        return Ok(None);
    };
    if if_statement.has_else {
        return Ok(None);
    }
    let condition = if_condition(ir, if_statement);
    let body = if_statement.if_stat;
    if let Some((instance_of, inverted)) = refinement_test(ir, condition) {
        let head = branch.get_basic_head(ir);
        if single_basic_expr(ir, head).is_some_and(|expr| var_assignment(ir, expr).is_some()) {
            edits.destroy.push(head);
        }
        let operands = instance_of_operands(ir, instance_of);
        let store = operands.get(2).copied().unwrap_or(operands[0]);
        let (binding, nested) = match ir[store].kind {
            ExprKind::Variable(_) => {
                let class = record_class(cx, &Expr::expr_type(cx, store));
                let ty = Expr::expr_type(cx, store);
                let record = class.map(|class| Record { class, store, ty });
                (Some(store), record)
            }
            ExprKind::Pattern(_) => (Some(store), None),
            _ => (None, None),
        };
        return Ok(Some(Refinement {
            body,
            inverted,
            binding,
            nested,
        }));
    }

    let Some(truth) = boolean_constant(cx, condition) else {
        return Ok(None);
    };
    let arm = if truth {
        Some(body.ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                "Constant record refinement has no body",
            )
        })?)
    } else {
        ir[branch].stats.get(index + 1).copied()
    };
    let Some(arm) = arm else { return Ok(None) };
    let head = arm.get_basic_head(ir);
    let Some(&first) = ir[head].exprents.and_then(|list| ir[list].first()) else {
        return Ok(None);
    };
    let Some(store) = var_assignment(ir, first) else {
        return Ok(None);
    };
    edits.remove_exprs.entry(head).or_default().push(first);
    Ok(Some(Refinement {
        body,
        inverted: !truth,
        binding: Some(store),
        nested: None,
    }))
}

fn if_condition(ir: &Ir, branch: IfStatement) -> ExprId {
    let head = branch
        .head_exprents
        .expect("Record refinement has no header");
    let ExprKind::If { condition } = ir[ir[head][0]].kind else {
        unreachable!("Expected an IfExprent");
    };
    condition
}

fn refinement_test(ir: &Ir, condition: ExprId) -> Option<(ExprId, bool)> {
    match &ir[condition].kind {
        ExprKind::Function {
            op: FunctionType::InstanceOf,
            ..
        } => Some((condition, false)),
        ExprKind::Function {
            op: FunctionType::BoolNot,
            operands,
            ..
        } if matches!(
            ir[operands[0]].kind,
            ExprKind::Function {
                op: FunctionType::InstanceOf,
                ..
            }
        ) =>
        {
            Some((operands[0], true))
        }
        _ => None,
    }
}

fn boolean_constant(cx: &Cx, expr: ExprId) -> Option<bool> {
    let ExprKind::Constant {
        value: ConstantValue::Integer(value),
        var_type,
        ..
    } = &cx.ir[expr].kind
    else {
        return None;
    };
    if !matches!(
        var_type.ty,
        CodeType::Boolean
            | CodeType::Char
            | CodeType::Byte
            | CodeType::Bytechar
            | CodeType::Short
            | CodeType::Shortchar
            | CodeType::Int
    ) {
        return None;
    }
    match value {
        0 => Some(false),
        1 if cx.options.boolean_as_int => Some(true),
        _ => None,
    }
}

fn single_basic_expr(ir: &Ir, stat: StatId) -> Option<ExprId> {
    if !matches!(ir[stat].kind, StatementKind::BasicBlock { .. }) {
        return None;
    }
    let [expr] = ir[ir[stat].exprents?].as_slice() else {
        return None;
    };
    Some(*expr)
}

fn var_assignment(ir: &Ir, expr: ExprId) -> Option<ExprId> {
    let (left, right) = ir[expr].as_assignment()?;
    Expr::variable(ir, left)?;
    Expr::variable(ir, right)?;
    Some(left)
}

fn instance_of_operands(ir: &Ir, expr: ExprId) -> &[ExprId] {
    let ExprKind::Function {
        op: FunctionType::InstanceOf,
        operands,
        ..
    } = &ir[expr].kind
    else {
        unreachable!("Expected an instanceof test");
    };
    operands
}

fn record_class(cx: &Cx, ty: &VarType) -> Option<Arc<StructClass>> {
    cx.classes().get_class(ty.value.as_deref()?)
}
