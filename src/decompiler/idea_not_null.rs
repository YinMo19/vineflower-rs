//! The bundled IdeaNotNull Java main-loop pass.

use std::io;
use std::sync::Arc;

use crate::code::cfg::basic_block::BasicBlock;
use crate::code::code_constants::ACC_STATIC;
use crate::decompiler::decompose::finish::condense_sequences;
use crate::decompiler::exps::{ExitType, Expr, ExprKind, FunctionType};
use crate::decompiler::ir::{EdgeId, ExprId, Ir, StatId};
use crate::decompiler::stats::{IfStatement, Statement, StatementKind};
use crate::engine::{
    Cx,
    counter_container::{CounterContainer, STATEMENT_COUNTER},
};
use crate::structs::{StructMember, StructMethod};
use crate::types::{CodeType, MethodDescriptor};

const NOT_NULL: &str = "org/jetbrains/annotations/NotNull";
const REPORT_NULL: &str = "$$$reportNull$$$0";

pub(crate) fn run(cx: &mut Cx, counters: &mut CounterContainer, root: StatId) -> io::Result<bool> {
    if !cx.options.idea_notnull || !cx.options.resugar_idea_notnull {
        return Ok(false);
    }
    let method = Arc::clone(root.method(&cx.ir));
    let mut changed = false;
    while let Some((statement, branch, edge)) = parameter_check(&cx.ir, root, &method) {
        remove_parameter_check(cx, counters, root, statement, branch, edge);
        validate_rewrite(&mut cx.ir, root)?;
        changed = true;
    }
    let return_is_not_null = method
        .attributes
        .runtime_invisible_annotations
        .as_ref()
        .is_some_and(|attr| {
            attr.annotations
                .iter()
                .any(|annotation| annotation.class_name == NOT_NULL)
        });
    if return_is_not_null {
        while let Some(check) = find_return_check(cx, root) {
            remove_return_check(&mut cx.ir, check);
            validate_rewrite(&mut cx.ir, root)?;
            changed = true;
        }
    }
    Ok(changed)
}

fn parameter_check(
    ir: &Ir,
    root: StatId,
    method: &StructMethod,
) -> Option<(StatId, StatId, EdgeId)> {
    let mut first = ir[root].first?;
    while matches!(ir[first].kind, StatementKind::Sequence) {
        first = ir[first].first?;
    }
    let StatementKind::If(header) = ir[first].kind else {
        return None;
    };
    let then = header.if_stat?;
    if header.else_stat.is_some() || !reports_null(ir, then) {
        return None;
    }
    let target = tested_for_null(ir, header)?;
    let variable = Expr::variable(ir, target)?;
    let attributes = method
        .attributes
        .runtime_invisible_parameter_annotations
        .as_ref()?;
    let descriptor = MethodDescriptor::parse_descriptor(&method.descriptor);
    let parameter = descriptor
        .parameter_slots(method.has_modifier(ACC_STATIC))
        .position(|(slot, _)| slot == variable.index)?;
    // Some compilers left out leading synthetic parameters from the attribute.
    let from_end = descriptor.params.len() - parameter;
    let annotation = attributes.param_annotations.len().checked_sub(from_end)?;
    let annotations = attributes.param_annotations.get(annotation)?;
    let edge = header.if_edge?;
    annotations
        .iter()
        .any(|annotation| annotation.class_name == NOT_NULL)
        .then_some((first, then, edge))
}

fn remove_parameter_check(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    root: StatId,
    statement: StatId,
    branch: StatId,
    edge: EdgeId,
) {
    let ir = &mut cx.ir;
    edge.remove(ir);
    let branch_id = ir[branch].id;
    ir[statement].stats.remove_with_key(&branch_id);
    if let Some(edge) = ir[branch].first_successor() {
        edge.remove(ir);
    }
    let block_id = counters.get_counter_and_increment(STATEMENT_COUNTER);
    let block = BasicBlock::new(ir, block_id);
    let empty = Statement::new_basic_block(ir, counters, block);
    ir[empty].exprents = Some(ir.new_list(Vec::new()));
    let parent = ir[statement]
        .parent
        .expect("Parameter check must have a parent");
    parent.replace_statement(ir, statement, empty);
    parent.set_all_parent(ir);
    condense_sequences(cx, counters, root);
}

enum ReturnCheck {
    IfElse {
        condition: StatId,
        branch: StatId,
        return_block: StatId,
        if_edge: EdgeId,
        else_edge: EdgeId,
    },
    Sequence {
        condition: StatId,
        return_block: StatId,
        next_edge: EdgeId,
        branch_edge: EdgeId,
    },
}

fn find_return_check(cx: &Cx, root: StatId) -> Option<ReturnCheck> {
    let mut pending = vec![root];
    while let Some(statement) = pending.pop() {
        if let Some(check) = match_return_check(cx, statement) {
            return Some(check);
        }
        pending.extend(cx.ir[statement].stats.iter().rev().copied());
    }
    None
}

fn match_return_check(cx: &Cx, statement: StatId) -> Option<ReturnCheck> {
    let ir = &cx.ir;
    let expr = only_expr(ir, statement)?;
    let ExprKind::Exit {
        kind: ExitType::Return,
        value: Some(return_value),
        ..
    } = ir[expr].kind
    else {
        return None;
    };
    let parent = ir[statement].parent?;
    match ir[parent].kind {
        StatementKind::If(header) if header.else_stat == Some(statement) => {
            let tested = tested_for_null(ir, header)?;
            let branch = header.if_stat?;
            if !Expr::equals(cx, tested, return_value)
                || !matches!(ir[only_expr(ir, branch)?].kind, ExprKind::Exit { .. })
            {
                return None;
            }
            Some(ReturnCheck::IfElse {
                condition: parent,
                branch,
                return_block: statement,
                if_edge: header.if_edge?,
                else_edge: header.else_edge?,
            })
        }
        StatementKind::Sequence => {
            let [.., condition, last] = &ir[parent].stats[..] else {
                return None;
            };
            if *last != statement {
                return None;
            }
            let StatementKind::If(header) = ir[*condition].kind else {
                return None;
            };
            let tested = tested_for_null(ir, header)?;
            let branch = header.if_stat?;
            if header.has_else
                || !reports_null(ir, branch)
                || !Expr::equals(cx, tested, return_value)
            {
                return None;
            }
            Some(ReturnCheck::Sequence {
                condition: *condition,
                return_block: statement,
                next_edge: ir[*condition].first_successor()?,
                branch_edge: ir[branch].first_successor()?,
            })
        }
        _ => None,
    }
}

fn remove_return_check(ir: &mut Ir, check: ReturnCheck) {
    match check {
        ReturnCheck::IfElse {
            condition,
            branch,
            return_block,
            if_edge,
            else_edge,
        } => {
            if_edge.remove(ir);
            else_edge.remove(ir);
            let (branch_id, return_id) = (ir[branch].id, ir[return_block].id);
            ir[condition].stats.remove_with_key(&branch_id);
            ir[condition].stats.remove_with_key(&return_id);
            if let Some(edge) = ir[branch].first_successor() {
                edge.remove(ir);
            }
            prepend_head(ir, condition, return_block);
            let parent = ir[condition]
                .parent
                .expect("Return check must have a parent");
            parent.replace_statement(ir, condition, return_block);
            parent.set_all_parent(ir);
        }
        ReturnCheck::Sequence {
            condition,
            return_block,
            next_edge,
            branch_edge,
        } => {
            next_edge.remove(ir);
            prepend_head(ir, condition, return_block);
            for edge in ir[condition].all_predecessors().to_vec() {
                edge.change_destination(ir, return_block);
            }
            branch_edge.remove(ir);
            let sequence = ir[condition]
                .parent
                .expect("Return check must belong to a sequence");
            let id = ir[condition].id;
            ir[sequence].stats.remove_with_key(&id);
            ir[sequence].first = ir[sequence].stats.first().copied();
        }
    }
}

fn prepend_head(ir: &mut Ir, condition: StatId, return_block: StatId) {
    let Some(prefix) = ir[condition].first.and_then(|head| ir[head].exprents) else {
        return;
    };
    let suffix = ir[return_block]
        .exprents
        .expect("Return block must have a return expression");
    if !ir[prefix].is_empty() {
        let expressions = ir[prefix].clone();
        ir[suffix].splice(..0, expressions);
    }
}

fn tested_for_null(ir: &Ir, header: IfStatement) -> Option<ExprId> {
    let condition = *ir[header.head_exprents?].first()?;
    let ExprKind::If { condition } = ir[condition].kind else {
        return None;
    };
    let ExprKind::Function {
        op: FunctionType::Eq,
        operands,
        ..
    } = &ir[condition].kind
    else {
        return None;
    };
    let [value, null] = operands.as_slice() else {
        return None;
    };
    matches!(&ir[*null].kind, ExprKind::Constant { var_type, .. } if var_type.ty == CodeType::Null)
        .then_some(*value)
}

fn only_expr(ir: &Ir, statement: StatId) -> Option<ExprId> {
    if matches!(ir[statement].kind, StatementKind::BasicBlock { .. })
        && let [expr] = ir[ir[statement].exprents?].as_slice()
    {
        Some(*expr)
    } else {
        None
    }
}

fn reports_null(ir: &Ir, statement: StatId) -> bool {
    only_expr(ir, statement).is_some_and(
        |expr| matches!(&ir[expr].kind, ExprKind::Invocation(call) if call.name == REPORT_NULL),
    )
}

#[cfg(debug_assertions)]
fn validate_rewrite(ir: &mut Ir, root: StatId) -> io::Result<()> {
    use rustc_hash::FxHashSet;

    let StatementKind::Root { dummy_exit, .. } = ir[root].kind else {
        unreachable!()
    };
    let mut statements = FxHashSet::default();
    let mut pending = vec![root, dummy_exit];
    let invalid = || {
        io::Error::new(
            io::ErrorKind::InvalidData,
            "Invalid statement graph after IdeaNotNull",
        )
    };
    while let Some(statement) = pending.pop() {
        let node = &ir[statement];
        if !statements.insert(statement) {
            return Err(invalid());
        }
        if !matches!(
            node.kind,
            StatementKind::BasicBlock { .. } | StatementKind::DummyExit { .. }
        ) && node.first.is_none_or(|first| !node.stats.contains(&first))
        {
            return Err(invalid());
        }
        for &child in &node.stats[..] {
            if ir[child].parent != Some(statement) {
                return Err(invalid());
            }
            pending.push(child);
        }
    }
    for statement in statements.iter().copied() {
        let node = &ir[statement];
        for edge in node
            .all_successors()
            .iter()
            .chain(node.all_predecessors())
            .chain(&node.label_edges)
        {
            let end = &ir[*edge];
            if !statements.contains(&end.source)
                || !statements.contains(&end.destination)
                || end
                    .closure
                    .is_some_and(|closure| !statements.contains(&closure))
                || !ir[end.source].all_successors().contains(edge)
                || !ir[end.destination].all_predecessors().contains(edge)
            {
                return Err(invalid());
            }
        }
    }
    crate::decompiler::flow::flatten::build_direct_graph(ir, root);
    Ok(())
}

#[cfg(not(debug_assertions))]
fn validate_rewrite(_: &mut Ir, _: StatId) -> io::Result<()> {
    Ok(())
}
