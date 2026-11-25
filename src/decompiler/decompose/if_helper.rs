// Copyright 2000-2020 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Combines conditional branches while expressions are simplified.

use rustc_hash::FxHashSet;

use super::finish::first_successor;
use crate::decompiler::assertions::assertion_field;
use crate::decompiler::exps::{Expr, ExprKind, FunctionType};
use crate::decompiler::ir::{EdgeId, ExprId, Ir, StatId};
use crate::decompiler::stats::stat_edge::{EdgeType, StatEdge};
use crate::decompiler::stats::{
    IfStatement, STATEDGE_ALL, STATEDGE_DIRECT_ALL, Statement, StatementKind,
};
use crate::engine::{Cx, counter_container::CounterContainer};
use crate::structs::StructClass;

pub fn merge_ifs(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    statement: StatId,
    reordered: &mut FxHashSet<i32>,
    class: &StructClass,
) -> bool {
    let mut changed = false;
    'merge: loop {
        let statements = match cx.ir[statement].kind {
            StatementKind::If(_) => vec![statement],
            StatementKind::Sequence => cx.ir[statement].stats.to_vec(),
            _ => return changed,
        };
        let single = statements.len() == 1;

        for stat in statements {
            if !matches!(cx.ir[stat].kind, StatementKind::If(_)) {
                continue;
            }
            let node = IfNode::build(&cx.ir, stat, single);
            if collapse_if_if(cx, counters, &node, class)
                || (!reordered.contains(&cx.ir[stat].id)
                    && (collapse_if_else(cx, counters, &node)
                        || collapse_else(cx, counters, &node)
                        || (cx.options.ternary_in_if && collapse_ternary(cx, counters, &node))
                        || if_else_chain_denesting(cx, counters, &node)))
            {
                changed = true;
                continue 'merge;
            }
            if reorder_if(cx, counters, stat) {
                changed = true;
                reordered.insert(cx.ir[stat].id);
                continue 'merge;
            }
        }
        return changed;
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum BranchType {
    Direct,
    Indirect,
    Else,
}

struct Branch<T> {
    kind: BranchType,
    target: T,
}

/// The root models its two destinations and one level of their outgoing edges.
struct IfNode {
    statement: StatId,
    inner: Branch<SubNode>,
    successor: Branch<SubNode>,
}

struct SubNode {
    statement: StatId,
    inner: Option<Branch<StatId>>,
    successor: Option<StatId>,
}

impl IfNode {
    fn build(ir: &Ir, statement: StatId, single: bool) -> Self {
        let branches = if_data(ir, statement);
        let inner = if let Some(target) = branches.if_stat {
            Branch {
                kind: BranchType::Direct,
                target: SubNode::build(ir, target),
            }
        } else {
            Branch {
                kind: BranchType::Indirect,
                target: SubNode::leaf(ir[branches.if_edge.unwrap()].destination),
            }
        };
        let successor = if branches.has_else {
            Branch {
                kind: BranchType::Else,
                target: SubNode::build(ir, branches.else_stat.unwrap()),
            }
        } else {
            let edge = outgoing(ir, statement);
            if single || ir[edge].edge_type != EdgeType::Regular {
                Branch {
                    kind: BranchType::Indirect,
                    target: SubNode::leaf(ir[edge].destination),
                }
            } else {
                Branch {
                    kind: BranchType::Direct,
                    target: SubNode::build(ir, ir[edge].destination),
                }
            }
        };
        Self {
            statement,
            inner,
            successor,
        }
    }
}

impl SubNode {
    fn leaf(statement: StatId) -> Self {
        Self {
            statement,
            inner: None,
            successor: None,
        }
    }

    fn build(ir: &Ir, statement: StatId) -> Self {
        let mut node = Self::leaf(statement);
        if let StatementKind::If(branches) = ir[statement].kind
            && !branches.has_else
        {
            node.inner = Some(Branch {
                kind: if branches.if_stat.is_some() {
                    BranchType::Direct
                } else {
                    BranchType::Indirect
                },
                target: ir[branches.if_edge.unwrap()].destination,
            });
        }
        node.successor = first_successor(ir, statement).map(|edge| ir[edge].destination);
        node
    }
}

fn collapse_if_if(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    root: &IfNode,
    class: &StructClass,
) -> bool {
    let nested = &root.inner.target;
    let Some(inner) = &nested.inner else {
        return false;
    };
    if root.inner.kind != BranchType::Direct
        || nested.successor != Some(root.successor.target.statement)
    {
        return false;
    }

    let parent = root.statement;
    let child = nested.statement;
    let parent_if = if_data(&cx.ir, parent);
    let child_if = if_data(&cx.ir, child);
    if !empty_if_head(&cx.ir, child)
        || child_if.has_ppmm
        || has_assert_field(cx, class, head_expr(&cx.ir, child_if))
    {
        return false;
    }

    let ir = &mut cx.ir;
    let parent_head = ir[parent].first.unwrap();
    parent_if.if_edge.unwrap().remove(ir);
    outgoing(ir, child).remove(ir);
    remove_child(ir, parent, child);

    let child_jump = child_if.if_edge.unwrap();
    if inner.kind == BranchType::Indirect {
        child_jump.change_source(ir, parent_head);
        // Upstream rewrites this field directly, leaving the detached child's labels alone.
        if ir[child_jump].closure == Some(child) {
            ir[child_jump].closure = None;
        }
        let branches = if_data_mut(ir, parent);
        branches.if_stat = None;
        branches.if_edge = Some(child_jump);
    } else {
        child_jump.remove(ir);
        let edge = add_regular_edge(ir, parent_head, inner.target);
        let branches = if_data_mut(ir, parent);
        branches.if_edge = Some(edge);
        branches.if_stat = Some(inner.target);
        add_child(ir, parent, inner.target);

        if let Some(edge) = first_successor(ir, inner.target)
            && ir[edge].closure == Some(child)
        {
            ir[edge].closure = Some(parent);
        }
    }

    let parent_expr = head_expr(ir, parent_if);
    let child_expr = head_expr(ir, child_if);
    let left = condition(ir, parent_expr);
    let right = condition(ir, child_expr);
    merge_conditions(
        ir,
        counters,
        parent_expr,
        FunctionType::BoolAnd,
        vec![left, right],
    );
    let offsets = ir[child_expr].bytecode.clone();
    Expr::add_offsets(ir, parent_expr, offsets.as_ref());
    true
}

fn collapse_if_else(cx: &mut Cx, counters: &mut CounterContainer, root: &IfNode) -> bool {
    let nested = &root.inner.target;
    let Some(inner) = &nested.inner else {
        return false;
    };
    if root.inner.kind != BranchType::Direct
        || root.successor.target.statement != inner.target
        || !empty_if_head(&cx.ir, nested.statement)
    {
        return false;
    }

    let ir = &mut cx.ir;
    let parent = root.statement;
    let child = nested.statement;
    let parent_if = if_data(ir, parent);
    let child_if = if_data(ir, child);
    let parent_head = ir[parent].first.unwrap();

    parent_if.if_edge.unwrap().remove(ir);
    child_if.if_edge.unwrap().remove(ir);
    remove_child(ir, parent, child);
    if_data_mut(ir, parent).if_stat = None;
    let edge = outgoing(ir, child);
    edge.change_source(ir, parent_head);
    if_data_mut(ir, parent).if_edge = Some(edge);

    let parent_expr = head_expr(ir, parent_if);
    let child_expr = head_expr(ir, child_if);
    let left = condition(ir, parent_expr);
    let right = negate(ir, counters, condition(ir, child_expr));
    merge_conditions(
        ir,
        counters,
        parent_expr,
        FunctionType::BoolAnd,
        vec![left, right],
    );
    let offsets = ir[child_expr].bytecode.clone();
    Expr::add_offsets(ir, parent_expr, offsets.as_ref());
    true
}

fn collapse_else(cx: &mut Cx, counters: &mut CounterContainer, root: &IfNode) -> bool {
    if root.successor.kind != BranchType::Direct {
        return false;
    }

    let first = root.statement;
    let nested = &root.successor.target;
    let second = nested.statement;
    let destination = root.inner.target.statement;
    let ir = &mut cx.ir;
    let first_if = if_data(ir, first);
    let first_jump = first_if.if_edge.unwrap();
    let first_expr = head_expr(ir, first_if);
    if let Some(inner) = &nested.inner {
        let invert = nested.successor == Some(destination);
        if (!invert && inner.target != destination) || !empty_if_head(ir, second) {
            return false;
        }

        first_jump.remove(ir);
        remove_successors_to(ir, first, second);
        for edge in first.get_predecessor_edges(ir, STATEDGE_ALL) {
            if !first.contains_statement_strict(ir, ir[edge].source) {
                edge.change_destination(ir, second);
            }
        }

        let parent = ir[first].parent.unwrap();
        remove_child(ir, parent, first);
        if ir[parent].first == Some(first) {
            ir[parent].first = Some(second);
        }

        let second_expr = head_expr(ir, if_data(ir, second));
        let mut left = condition(ir, first_expr);
        let op = if invert {
            left = negate(ir, counters, left);
            FunctionType::BoolAnd
        } else {
            FunctionType::BoolOr
        };
        let right = condition(ir, second_expr);
        merge_conditions(ir, counters, second_expr, op, vec![left, right]);

        if !empty_if_head(ir, first) {
            second.replace_statement(ir, ir[second].first.unwrap(), ir[first].first.unwrap());
        }
        return true;
    }

    if nested.successor != Some(destination) {
        return false;
    }

    remove_successors_to(ir, first, second);
    for edge in second.get_successor_edges(ir, STATEDGE_ALL) {
        edge.change_source(ir, first);
    }
    first_jump.remove(ir);
    let replacement = StatEdge::new(
        ir,
        ir[first_jump].edge_type,
        second,
        ir[first_jump].destination,
        ir[first_jump].closure,
    );
    second.add_successor(ir, replacement);

    let new_jump = add_regular_edge(ir, ir[first].first.unwrap(), second);
    let branches = if_data_mut(ir, first);
    branches.if_edge = Some(new_jump);
    branches.if_stat = Some(second);

    add_child(ir, first, second);
    remove_child(ir, ir[first].parent.unwrap(), second);

    negate_condition(ir, counters, first_expr);
    true
}

fn collapse_ternary(cx: &mut Cx, counters: &mut CounterContainer, root: &IfNode) -> bool {
    if root.inner.kind != BranchType::Direct || root.successor.kind != BranchType::Else {
        return false;
    }

    let then_node = &root.inner.target;
    let else_node = &root.successor.target;
    let (Some(then_inner), Some(then_next), Some(else_inner), Some(else_next)) = (
        &then_node.inner,
        then_node.successor,
        &else_node.inner,
        else_node.successor,
    ) else {
        return false;
    };
    let ir = &mut cx.ir;
    let first = then_node.statement;
    let second = else_node.statement;
    if then_inner.kind != BranchType::Indirect
        || else_inner.kind != BranchType::Indirect
        || !empty_if_head(ir, first)
        || !empty_if_head(ir, second)
    {
        return false;
    }

    let invert = if then_inner.target == else_inner.target && then_next == else_next {
        false
    } else if then_inner.target == else_next && then_next == else_inner.target {
        true
    } else {
        return false;
    };

    let main = root.statement;
    let main_head = ir[main].first.unwrap();
    let main_if = if_data(ir, main);
    let first_if = if_data(ir, first);
    let second_if = if_data(ir, second);

    remove_child(ir, main, first);
    main_if.if_edge.unwrap().remove(ir);
    if_data_mut(ir, main).if_stat = None;

    remove_child(ir, main, second);
    main_if.else_edge.unwrap().remove(ir);
    if_data_mut(ir, main).else_stat = None;

    first_if.if_edge.unwrap().remove(ir);
    outgoing(ir, first).remove(ir);

    let jump = second_if.if_edge.unwrap();
    if_data_mut(ir, main).if_edge = Some(jump);
    jump.change_source(ir, main_head);

    if let Some(edge) = first_successor(ir, main) {
        edge.remove(ir);
    }
    let next = outgoing(ir, second);
    if ir[next].closure == Some(second) {
        next.remove_closure(ir);
    }
    next.change_source(ir, main);
    let next = outgoing(ir, main);
    if ir[next].closure == Some(main) {
        if ir[next].source != main {
            next.remove_closure(ir);
        }
        next.change_type(ir, EdgeType::Regular);
    }

    let branches = if_data_mut(ir, main);
    branches.has_else = false;
    branches.else_edge = None;

    let head = head_expr(ir, main_if);
    let test = condition(ir, head);
    let mut yes = condition(ir, head_expr(ir, first_if));
    if invert {
        yes = negate(ir, counters, yes);
    }
    let no = condition(ir, head_expr(ir, second_if));
    merge_conditions(
        ir,
        counters,
        head,
        FunctionType::Ternary,
        vec![test, yes, no],
    );
    true
}

fn if_else_chain_denesting(cx: &mut Cx, counters: &mut CounterContainer, root: &IfNode) -> bool {
    if root.inner.kind != BranchType::Direct || root.successor.kind == BranchType::Else {
        return false;
    }

    let ir = &mut cx.ir;
    let outer = root.statement;
    let parent = ir[outer].parent.unwrap();
    if !matches!(ir[parent].kind, StatementKind::Sequence) {
        return false;
    }

    let nested = root.inner.target.statement;
    let last = *ir[parent].stats.get_last();
    if !has_direct_end_edge(ir, nested, parent) || !has_direct_end_edge(ir, last, parent) {
        return false;
    }

    let Some(nested_if) = leading_if(ir, nested) else {
        return false;
    };
    let Some(then_branch) = if_data(ir, nested_if).if_stat else {
        return false;
    };
    if !empty_if_head(ir, nested_if) || !has_direct_end_edge(ir, then_branch, parent) {
        return false;
    }

    let Some(next) =
        first_successor(ir, outer).filter(|&edge| ir[edge].edge_type == EdgeType::Regular)
    else {
        return false;
    };
    if leading_if(ir, ir[next].destination).is_some_and(|next_if| empty_if_head(ir, next_if)) {
        return false;
    }

    let head = head_expr(ir, if_data(ir, outer));
    negate_condition(ir, counters, head);
    swap_branches(ir, counters, outer, parent);
    true
}

fn reorder_if(cx: &mut Cx, counters: &mut CounterContainer, stat: StatId) -> bool {
    let ir = &mut cx.ir;
    let branches = if_data(ir, stat);
    if branches.has_else {
        return false;
    }

    let parent = ir[stat].parent.unwrap();
    let parent_is_sequence = matches!(ir[parent].kind, StatementKind::Sequence);
    let from = if parent_is_sequence { parent } else { stat };
    let next = get_next_statement(ir, from);

    let then_branch = branches.if_stat;
    let jump = branches.if_edge.unwrap();
    let if_direct = match then_branch {
        Some(branch) => has_finally_exit(ir, branch) || has_direct_end_edge(ir, branch, from),
        None => {
            ir[jump].edge_type == EdgeType::FinallyExit
                || is_direct_path(ir, from, ir[jump].destination)
        }
    };
    let last = if parent_is_sequence {
        *ir[parent].stats.get_last()
    } else {
        stat
    };
    let no_else = last == stat;
    let else_direct = has_finally_exit(ir, last) || has_direct_end_edge(ir, last, from);

    let successor = outgoing(ir, stat);
    if !no_else && exists_path(ir, stat, ir[successor].destination) {
        return false;
    }

    let if_direct_path = !if_direct && then_branch.is_some() && exists_path(ir, stat, next);
    let else_direct_path = !else_direct
        && !no_else
        && ir[parent]
            .stats
            .iter()
            .rev()
            .take_while(|&&child| child != stat)
            .any(|&child| exists_path(ir, child, next));

    if (if_direct || if_direct_path)
        && (else_direct || else_direct_path)
        && then_branch.is_some()
        && !no_else
    {
        let else_branch = take_following_statements(ir, counters, stat, parent);
        let new_jump = add_regular_edge(ir, ir[stat].first.unwrap(), else_branch);
        let branches = if_data_mut(ir, stat);
        branches.else_stat = Some(else_branch);
        branches.else_edge = Some(new_jump);
        add_child(ir, stat, else_branch);
        if_data_mut(ir, stat).has_else = true;
    } else if if_direct && (!else_direct || (then_branch.is_none() && !no_else)) {
        let head = head_expr(ir, branches);
        negate_condition(ir, counters, head);

        if no_else {
            let head_stat = ir[stat].first.unwrap();
            if let Some(then_branch) = then_branch {
                let sequence = Statement::new_sequence(ir, counters, &[stat, then_branch]);

                jump.remove(ir);
                remove_child(ir, stat, then_branch);
                if_data_mut(ir, stat).if_stat = None;

                reattach_edge(ir, successor, head_stat);
                if_data_mut(ir, stat).if_edge = Some(successor);

                parent.replace_statement(ir, stat, sequence);
                sequence.set_all_parent(ir);
                add_regular_edge(ir, stat, then_branch);
            } else {
                jump.remove(ir);
                successor.remove(ir);

                ir[jump].source = stat;
                ir[successor].source = head_stat;

                stat.add_successor(ir, jump);
                head_stat.add_successor(ir, successor);
                if_data_mut(ir, stat).if_edge = Some(successor);
            }
        } else {
            swap_branches(ir, counters, stat, parent);
        }
    } else {
        return false;
    }

    true
}

fn swap_branches(ir: &mut Ir, counters: &mut CounterContainer, stat: StatId, parent: StatId) {
    let branches = if_data(ir, stat);
    debug_assert!(!branches.has_else);
    let body = take_following_statements(ir, counters, stat, parent);
    let jump = branches.if_edge.unwrap();

    if let Some(then_branch) = branches.if_stat {
        jump.remove(ir);
        remove_child(ir, stat, then_branch);
        add_regular_edge(ir, stat, then_branch);
        add_child(ir, parent, then_branch);
    } else {
        reattach_edge(ir, jump, stat);
    }

    let new_jump = add_regular_edge(ir, ir[stat].first.unwrap(), body);
    let branches = if_data_mut(ir, stat);
    branches.if_stat = Some(body);
    branches.if_edge = Some(new_jump);
    add_child(ir, stat, body);
}

fn take_following_statements(
    ir: &mut Ir,
    counters: &mut CounterContainer,
    stat: StatId,
    sequence: StatId,
) -> StatId {
    let index = ir[sequence].stats.get_index_by_key(&ir[stat].id);
    let following: Vec<_> = ir[sequence].stats.iter().skip(index + 1).copied().collect();
    let body = if let [only] = following.as_slice() {
        *only
    } else {
        let body = Statement::new_sequence(ir, counters, &following);
        body.set_all_parent(ir);
        body
    };

    outgoing(ir, stat).remove(ir);
    for child in following {
        remove_child(ir, sequence, child);
    }
    body
}

fn has_direct_end_edge(ir: &Ir, stat: StatId, from: StatId) -> bool {
    if stat
        .get_successor_edges(ir, STATEDGE_ALL)
        .into_iter()
        .any(|edge| is_direct_path(ir, from, ir[edge].destination))
    {
        return true;
    }
    if ir[stat].exprents.is_some() {
        return false;
    }

    let children = &ir[stat].stats;
    match &ir[stat].kind {
        StatementKind::Sequence => has_direct_end_edge(ir, *children.get_last(), from),
        StatementKind::CatchAll { .. } | StatementKind::Catch { .. } | StatementKind::Switch(_) => {
            children
                .iter()
                .any(|&child| has_direct_end_edge(ir, child, from))
        }
        StatementKind::If(branches) if branches.has_else => {
            has_direct_end_edge(ir, branches.if_stat.unwrap(), from)
                || has_direct_end_edge(ir, branches.else_stat.unwrap(), from)
        }
        StatementKind::Synchronized { .. } => has_direct_end_edge(ir, children[1], from),
        _ => false,
    }
}

/// The destination reached after a statement finishes, as in MergeHelper.isDirectPath.
fn is_direct_path(ir: &Ir, mut stat: StatId, end: StatId) -> bool {
    loop {
        let edges = stat.get_successor_edges(ir, STATEDGE_DIRECT_ALL);
        if !edges.is_empty() {
            return edges.into_iter().any(|edge| ir[edge].destination == end);
        }

        let Some(parent) = ir[stat].parent else {
            return matches!(ir[end].kind, StatementKind::DummyExit);
        };
        match &ir[parent].kind {
            StatementKind::Root { .. } => return matches!(ir[end].kind, StatementKind::DummyExit),
            StatementKind::Do => return end == parent,
            StatementKind::Switch(switch) => {
                for cases in switch.cases.windows(2) {
                    if cases[0].statement == stat {
                        let mut next = cases[1].statement;
                        if ir[next].exprents.is_some_and(|list| ir[list].is_empty()) {
                            next = ir[outgoing(ir, next)].destination;
                        }
                        return end == next;
                    }
                }
            }
            _ => {}
        }
        stat = parent;
    }
}

fn get_next_statement(ir: &Ir, mut stat: StatId) -> StatId {
    loop {
        let parent = ir[stat].parent.expect("Statement has no enclosing root");
        match &ir[parent].kind {
            StatementKind::Root { dummy_exit, .. } => return *dummy_exit,
            StatementKind::Do => return parent,
            StatementKind::Sequence => {
                let children = &ir[parent].stats;
                if *children.get_last() != stat
                    && let Some(index) = children.iter().rposition(|&child| child == stat)
                {
                    return children[index + 1];
                }
            }
            _ => {}
        }
        stat = parent;
    }
}

fn exists_path(ir: &Ir, from: StatId, to: StatId) -> bool {
    to.get_predecessor_edges(ir, STATEDGE_ALL)
        .into_iter()
        .any(|edge| from.contains_statement_strict(ir, ir[edge].source))
}

fn has_assert_field(cx: &Cx, class: &StructClass, expr: ExprId) -> bool {
    let Some((holder, field)) = assertion_field(cx, class) else {
        return false;
    };
    Expr::all_exprents(&cx.ir, expr, true, true)
        .into_iter()
        .any(|expr| {
            matches!(&cx.ir[expr].kind, ExprKind::Field(reference)
                if reference.name == field.name
                    && reference.classname.as_ref() == Some(&holder.qualified_name))
        })
}

fn leading_if(ir: &Ir, stat: StatId) -> Option<StatId> {
    match ir[stat].kind {
        StatementKind::If(_) => Some(stat),
        StatementKind::Sequence => ir[stat]
            .first
            .filter(|&child| matches!(ir[child].kind, StatementKind::If(_))),
        _ => None,
    }
}

fn empty_if_head(ir: &Ir, stat: StatId) -> bool {
    let head = ir[stat].first.unwrap();
    ir[ir[head].exprents.expect("If head has no expression list")].is_empty()
}

fn has_finally_exit(ir: &Ir, stat: StatId) -> bool {
    first_successor(ir, stat).is_some_and(|edge| ir[edge].edge_type == EdgeType::FinallyExit)
}

fn outgoing(ir: &Ir, stat: StatId) -> EdgeId {
    first_successor(ir, stat)
        .unwrap_or_else(|| panic!("Statement {} has no successors", ir[stat].id))
}

fn remove_successors_to(ir: &mut Ir, source: StatId, destination: StatId) {
    for edge in source.get_successor_edges(ir, STATEDGE_ALL) {
        if ir[edge].destination == destination {
            edge.remove(ir);
        }
    }
}

fn add_regular_edge(ir: &mut Ir, source: StatId, destination: StatId) -> EdgeId {
    let edge = StatEdge::new(ir, EdgeType::Regular, source, destination, None);
    source.add_successor(ir, edge);
    edge
}

fn reattach_edge(ir: &mut Ir, edge: EdgeId, source: StatId) {
    edge.remove(ir);
    ir[edge].source = source;
    source.add_successor(ir, edge);
}

fn add_child(ir: &mut Ir, parent: StatId, child: StatId) {
    let id = ir[child].id;
    ir[parent].stats.add_with_key(child, id);
    ir[child].parent = Some(parent);
}

fn remove_child(ir: &mut Ir, parent: StatId, child: StatId) {
    let id = ir[child].id;
    ir[parent].stats.remove_with_key(&id);
}

fn if_data(ir: &Ir, stat: StatId) -> IfStatement {
    let StatementKind::If(branches) = ir[stat].kind else {
        unreachable!("Expected an if statement");
    };
    branches
}

fn if_data_mut(ir: &mut Ir, stat: StatId) -> &mut IfStatement {
    let StatementKind::If(branches) = &mut ir[stat].kind else {
        unreachable!("Expected an if statement");
    };
    branches
}

fn head_expr(ir: &Ir, branches: IfStatement) -> ExprId {
    ir[branches.head_exprents.unwrap()][0]
}

fn condition(ir: &Ir, head: ExprId) -> ExprId {
    let ExprKind::If { condition } = ir[head].kind else {
        unreachable!("Expected an if expression");
    };
    condition
}

fn negate(ir: &mut Ir, counters: &mut CounterContainer, condition: ExprId) -> ExprId {
    Expr::function(ir, counters, FunctionType::BoolNot, vec![condition], None)
}

fn negate_condition(ir: &mut Ir, counters: &mut CounterContainer, head: ExprId) {
    let condition = negate(ir, counters, condition(ir, head));
    ir[head].kind = ExprKind::If { condition };
}

fn merge_conditions(
    ir: &mut Ir,
    counters: &mut CounterContainer,
    head: ExprId,
    op: FunctionType,
    operands: Vec<ExprId>,
) {
    let condition = Expr::function(ir, counters, op, operands, None);
    ir[head].kind = ExprKind::If { condition };
}
