// Copyright 2000-2024 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! References retained by published method and class wrappers.

use super::{ExprId, Ir, IrNode};
use crate::decompiler::exps::{Expr, ExprKind, SwitchCaseValues};
use crate::decompiler::stats::{DoStatement, IfStatement, Statement, StatementKind};

/// At a built-in driver boundary all method passes using CFG topology have
/// returned. Nested-class and writer passes traverse statements and direct
/// graphs. Their basic blocks still own instruction sequences and old offsets.
pub(super) fn visit_published(ir: &mut Ir, node: IrNode, mut visit: impl FnMut(IrNode)) {
    match node {
        IrNode::Stat(stat) => visit_statement(&ir[stat], visit),
        IrNode::Edge(edge) => {
            let edge = &ir[edge];
            visit(edge.source.into());
            visit(edge.destination.into());
            if let Some(closure) = edge.closure {
                visit(closure.into());
            }
        }
        IrNode::Expr(expr) => visit_expression(ir, expr, visit),
        IrNode::List(list) => {
            for &expr in &ir[list] {
                visit(expr.into());
            }
        }
        IrNode::Block(block) => {
            let block = &mut ir[block];
            block.preds = Vec::new();
            block.succs = Vec::new();
            block.pred_exceptions = Vec::new();
            block.succ_exceptions = Vec::new();
        }
        IrNode::VarProcessor(_) => {}
    }
}

fn visit_statement(stat: &Statement, mut visit: impl FnMut(IrNode)) {
    for child in [stat.first, stat.parent, stat.post]
        .into_iter()
        .flatten()
        .chain(stat.stats.iter().copied())
        .chain(stat.continue_set.iter().copied())
    {
        visit(child.into());
    }
    // Visit each view since temporary cleanup can change them independently.
    for edge in stat.indexed_edges().chain(stat.label_edges.iter().copied()) {
        visit(edge.into());
    }
    if let Some(list) = stat.exprents {
        visit(list.into());
    }
    for &definition in &stat.var_definitions {
        visit(definition.into());
    }
    match &stat.kind {
        StatementKind::BasicBlock { block } => visit((*block).into()),
        StatementKind::Do(DoStatement {
            init,
            condition,
            increment,
            ty: _,
        }) => {
            for list in [*init, *condition, *increment].into_iter().flatten() {
                visit(list.into());
            }
        }
        StatementKind::Switch(switch) => {
            if let Some(list) = switch.head_exprents {
                visit(list.into());
            }
            if let Some(edge) = switch.default_edge {
                visit(edge.into());
            }
            for &stat in &switch.scoped_case_statements {
                visit(stat.into());
            }
            for case in &switch.cases {
                visit(case.statement.into());
                for &edge in &case.edges {
                    visit(edge.into());
                }
            }
            for &expr in switch
                .case_values()
                .flatten()
                .flatten()
                .chain(switch.case_guards.iter().flatten())
            {
                visit(expr.into());
            }
        }
        StatementKind::If(IfStatement {
            if_stat,
            else_stat,
            if_edge,
            else_edge,
            head_exprents,
            ..
        }) => {
            for branch in [*if_stat, *else_stat].into_iter().flatten() {
                visit(branch.into());
            }
            for edge in [*if_edge, *else_edge].into_iter().flatten() {
                visit(edge.into());
            }
            if let Some(list) = head_exprents {
                visit((*list).into());
            }
        }
        StatementKind::Catch {
            vars, resources, ..
        } => {
            for &var in vars {
                visit(var.into());
            }
            if let Some(list) = resources {
                visit((*list).into());
            }
        }
        StatementKind::CatchAll {
            handler,
            monitor,
            vars,
            ..
        } => {
            if let Some(handler) = handler {
                visit((*handler).into());
            }
            for &expr in monitor.iter().chain(vars) {
                visit(expr.into());
            }
        }
        StatementKind::Synchronized {
            body,
            head_exprents,
        } => {
            visit((*body).into());
            if let Some(list) = head_exprents {
                visit((*list).into());
            }
        }
        StatementKind::Root { dummy_exit, .. } => visit((*dummy_exit).into()),
        StatementKind::General { .. }
        | StatementKind::Sequence
        | StatementKind::DummyExit { .. } => {}
    }
}

fn visit_expression(ir: &Ir, expr: ExprId, mut visit: impl FnMut(IrNode)) {
    match &ir[expr].kind {
        ExprKind::Variable(var) => {
            if let Some(processor) = var.processor {
                visit(processor.into());
            }
        }
        ExprKind::New {
            dimensions,
            constructor,
            array_elements,
            ..
        } => {
            // The constructor invocation has its own arena identity.
            for &expr in constructor.iter().chain(dimensions).chain(array_elements) {
                visit(expr.into());
            }
        }
        ExprKind::SwitchHead { value, case_values } => {
            visit((*value).into());
            match case_values {
                Some(SwitchCaseValues::Statement(stat)) => visit((*stat).into()),
                Some(SwitchCaseValues::Copied(cases)) => {
                    for &expr in cases.iter().flatten().flatten() {
                        visit(expr.into());
                    }
                }
                None => {}
            }
        }
        ExprKind::Switch { backing, .. } => visit((*backing).into()),
        _ => {
            for child in Expr::children(ir, expr) {
                visit(child.into());
            }
        }
    }
}
