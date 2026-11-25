// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Conditional rewrites interleaved with stack-expression simplification.

use std::{
    io,
    sync::{Arc, LazyLock},
};

use crate::decompiler::decompose::finish::destroy_and_flatten_statement;
use crate::decompiler::exps::{ExitType, Expr, ExprKind, FunctionType};
use crate::decompiler::ir::{EdgeId, ExprId, Ir, StatId};
use crate::decompiler::sforms::SsaResult;
use crate::decompiler::stats::{
    STATEDGE_ALL, StatementKind,
    stat_edge::{EdgeType, StatEdge},
};
use crate::engine::{Cx, counter_container::CounterContainer};
use crate::structs::{
    StructClass,
    matcher::{Capture, Matcher, Object},
};
use crate::types::{MethodDescriptor, VarType};
use crate::util::interpreter_util::make_unique_key;

enum ResultKind {
    Assignment(ExprId),
    Return(Option<VarType>, Arc<MethodDescriptor>),
}

pub(super) fn build_iff(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    stat: StatId,
    ssa: Option<&SsaResult>,
) -> io::Result<bool> {
    let ir = &mut cx.ir;
    let StatementKind::If(branch) = ir[stat].kind else {
        return Ok(false);
    };
    if ir[stat].exprents.is_some() || !branch.has_else {
        return Ok(false);
    }
    let Some((then_expr, exit)) = single_branch(ir, branch.if_stat) else {
        return Ok(false);
    };
    let Some((else_expr, else_exit)) = single_branch(ir, branch.else_stat) else {
        return Ok(false);
    };
    if ir[exit].destination != ir[else_exit].destination {
        return Ok(false);
    }

    let (yes, no, result) = match (&ir[then_expr].kind, &ir[else_expr].kind) {
        (
            ExprKind::Assignment { left, right, .. },
            ExprKind::Assignment {
                left: other,
                right: alternate,
                ..
            },
        ) => {
            let (ExprKind::Variable(a), ExprKind::Variable(b)) =
                (&ir[*left].kind, &ir[*other].kind)
            else {
                return Ok(false);
            };
            if !a.stack || a.index != b.index {
                return Ok(false);
            }
            let ssa = ssa.ok_or_else(|| {
                io::Error::new(
                    io::ErrorKind::InvalidData,
                    "Trying to make ternary but have no SSA-Form! How is this possible?",
                )
            })?;
            if !ssa.versions.phi.iter().any(|(key, versions)| {
                key.var == a.index && versions.contains(&a.version) && versions.contains(&b.version)
            }) {
                return Ok(false);
            }
            (*right, *alternate, ResultKind::Assignment(*left))
        }
        (
            ExprKind::Exit {
                kind: ExitType::Return,
                value: Some(yes),
                return_type,
                method_descriptor,
            },
            ExprKind::Exit {
                kind: ExitType::Return,
                value: Some(no),
                ..
            },
        ) => {
            if [yes, no].into_iter().any(|value| {
                matches!(
                    ir[*value].kind,
                    ExprKind::Function {
                        op: FunctionType::Ternary,
                        ..
                    }
                )
            }) {
                return Ok(false);
            }
            (
                *yes,
                *no,
                ResultKind::Return(return_type.clone(), Arc::clone(method_descriptor)),
            )
        }
        _ => return Ok(false),
    };
    let head = ir[branch.head_exprents.unwrap()][0];
    let ExprKind::If { condition } = ir[head].kind else {
        unreachable!()
    };
    let bytecode = ir[head].bytecode.clone();
    let ternary = Expr::function(
        ir,
        counters,
        FunctionType::Ternary,
        vec![condition, yes, no],
        bytecode.clone(),
    );
    let is_return = matches!(result, ResultKind::Return(..));
    let result = match result {
        ResultKind::Assignment(left) => ExprKind::Assignment {
            left,
            right: ternary,
            compound: None,
        },
        ResultKind::Return(return_type, method_descriptor) => ExprKind::Exit {
            kind: ExitType::Return,
            value: Some(ternary),
            return_type,
            method_descriptor,
        },
    };
    let expr = Expr::new(ir, counters, result, bytecode);
    let mut body = ir[ir[ir[stat].first.unwrap()].exprents.unwrap()].clone();
    body.push(expr);
    ir[stat].exprents = Some(ir.new_list(body));

    let parent = ir[stat].parent.unwrap();
    let dest = ir[exit].destination;
    if is_return {
        let closure = ir[exit]
            .closure
            .map(|id| if id == stat { parent } else { id });
        let edge = StatEdge::new(ir, EdgeType::Break, stat, dest, closure);
        stat.add_successor(ir, edge);
    } else if stat.get_successor_edges(ir, STATEDGE_ALL).is_empty() {
        let edge = StatEdge::new(ir, ir[exit].edge_type, stat, dest, None);
        stat.add_successor(ir, edge);
        if let Some(closure) = ir[exit].closure {
            closure.add_labeled_edge(ir, edge);
        }
    }
    destroy_and_flatten_statement(cx, counters, parent, stat);
    Ok(true)
}

fn single_branch(ir: &Ir, branch: Option<StatId>) -> Option<(ExprId, EdgeId)> {
    let branch = branch?;
    let [expr] = ir[ir[branch].exprents?][..] else {
        return None;
    };
    let edges = branch.get_successor_edges(ir, STATEDGE_ALL);
    let [exit] = edges[..] else { return None };
    Some((expr, exit))
}

static CLASS_LITERAL: LazyLock<Matcher> = LazyLock::new(|| {
    Matcher::new(&[
        "statement type:if iftype:if exprsize:-1",
        " exprent position:head type:if",
        "  exprent type:function functype:eq",
        "   exprent type:field name:$fieldname$",
        "   exprent type:constant consttype:null",
        " statement type:basicblock",
        "  exprent position:-1 type:assignment ret:$assignfield$",
        "   exprent type:var index:$var$",
        "   exprent type:field name:$fieldname$",
        " statement type:sequence statsize:2",
        "  statement type:trycatch",
        "   statement type:basicblock exprsize:1",
        "    exprent type:assignment",
        "     exprent type:var index:$var$",
        "     exprent type:invocation invclass:java/lang/Class signature:forName(Ljava/lang/String;)Ljava/lang/Class;",
        "      exprent position:0 type:constant consttype:string constvalue:$classname$",
        "   statement type:basicblock exprsize:1",
        "    exprent type:exit exittype:throw",
        "  statement type:basicblock exprsize:1",
        "   exprent type:assignment",
        "    exprent type:field name:$fieldname$ ret:$field$",
        "    exprent type:var index:$var$",
    ])
});

pub(super) fn collapse_class_literal(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    stat: StatId,
    class: &StructClass,
) -> bool {
    let Some(captures) = CLASS_LITERAL.matches(cx, Object::Statement(stat)) else {
        return false;
    };
    let (
        Some(Capture::Value(name)),
        Some(Capture::Object(Object::Expression(assign))),
        Some(Capture::Object(Object::Expression(field))),
    ) = (
        captures.get("$classname$"),
        captures.get("$assignfield$"),
        captures.get("$field$"),
    )
    else {
        unreachable!()
    };
    let ir = &mut cx.ir;
    let ExprKind::Assignment { right, .. } = ir[*assign].kind else {
        unreachable!()
    };
    let class_ref = Expr::constant(VarType::VARTYPE_CLASS, name.clone(), false);
    let new = Expr::new(ir, counters, class_ref, None);
    Expr::replace(ir, *assign, right, new);
    let body = ir[ir[ir[stat].first.unwrap()].exprents.unwrap()].clone();
    ir[stat].exprents = Some(ir.new_list(body));
    let parent = ir[stat].parent.unwrap();
    destroy_and_flatten_statement(cx, counters, parent, stat);
    if let Some(owner) = cx.class_nodes.id(&class.qualified_name) {
        let ExprKind::Field(field) = &cx.ir[*field].kind else {
            unreachable!()
        };
        cx.class_nodes[owner].hidden_members.insert(make_unique_key(
            &field.name,
            &field.descriptor.descriptor_string,
        ));
    }
    true
}
