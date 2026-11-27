//! Simple statement recognizers invoked by `DomHelper.detectStatement`.

mod dec_helper;
mod switch;

pub(crate) use switch::sort_edges_and_nodes as sort_switch_edges;
pub(super) use switch::can_sort as can_sort_switch;

use std::sync::Arc;

use arcstr::ArcStr;

use self::dec_helper::{
    check_statement_exceptions, get_unique_pred_exceptions, invalid_head_merge, is_choice_statement,
};
use super::EdgeDirection::{Backward, Forward};
use super::stat_edge::EdgeType;
use super::{
    DoStatement, IfStatement, LastBasicType, STATEDGE_DIRECT_ALL, Statement, StatementKind,
    SwitchStatement,
};
use crate::code::InstructionSequence;
use crate::code::cfg::basic_block::BasicBlock;
use crate::decompiler::ir::{EdgeId, Expr, ExprId, Ir, StatId};
use crate::engine::counter_container::{CounterContainer, STATEMENT_COUNTER};
use crate::types::{CodeType, VarType};

pub fn detect_statement(
    ir: &mut Ir,
    counters: &mut CounterContainer,
    head: StatId,
    try_loop_fix: bool,
) -> Option<StatId> {
    detect_do(ir, counters, head)
        .or_else(|| switch::detect_switch(ir, counters, head))
        .or_else(|| detect_if(ir, counters, head))
        .or_else(|| detect_sequence(ir, counters, head))
        .or_else(|| detect_catch(ir, counters, head, try_loop_fix))
        .or_else(|| detect_catch_all(ir, counters, head, try_loop_fix))
}

fn with_head(
    ir: &Ir,
    counters: &mut CounterContainer,
    kind: StatementKind,
    head: StatId,
) -> Statement {
    let mut statement = Statement::new(kind, counters.get_counter_and_increment(STATEMENT_COUNTER));
    statement.first = Some(head);
    statement.stats.add_with_key(head, ir[head].id);
    statement
}

fn first_direct_edge(ir: &Ir, head: StatId) -> Option<EdgeId> {
    ir[head]
        .edge_view(Forward, STATEDGE_DIRECT_ALL)
        .first()
        .copied()
}

fn regular_successor(ir: &Ir, head: StatId) -> Option<StatId> {
    first_direct_edge(ir, head)
        .filter(|&edge| ir[edge].edge_type == EdgeType::Regular)
        .map(|edge| ir[edge].destination)
}

fn detect_do(ir: &mut Ir, counters: &mut CounterContainer, head: StatId) -> Option<StatId> {
    if ir[head].last_basic_type != LastBasicType::General || ir[head].is_monitor_enter {
        return None;
    }

    let is_loop = match regular_successor(ir, head) {
        Some(target) => target == head,
        None => {
            !matches!(ir[head].kind, StatementKind::Do(_))
                && ir[head].continue_set.contains(&head.get_basic_head(ir))
        }
    };
    is_loop.then(|| {
        ir.stats.push(with_head(
            ir,
            counters,
            StatementKind::Do(DoStatement::default()),
            head,
        ))
    })
}

fn detect_sequence(ir: &mut Ir, counters: &mut CounterContainer, head: StatId) -> Option<StatId> {
    if ir[head].last_basic_type != LastBasicType::General {
        return None;
    }
    let tail = regular_successor(ir, head)?;
    if tail == head
        || ir[tail].edge_view(Backward, EdgeType::Regular.mask()).len() != 1
        || ir[tail].is_monitor_enter
        || ir[tail].last_basic_type != LastBasicType::General
        || !check_statement_exceptions(ir, &[head, tail])
    {
        return None;
    }

    let statement = Statement::new_sequence(ir, counters, &[head, tail]);
    ir[statement].post = regular_successor(ir, tail).filter(|&target| target != head);
    Some(statement)
}

fn detect_if(ir: &mut Ir, counters: &mut CounterContainer, head: StatId) -> Option<StatId> {
    if !matches!(ir[head].kind, StatementKind::BasicBlock { .. })
        || ir[head].last_basic_type != LastBasicType::If
    {
        return None;
    }

    let regular = ir[head].edge_view(Forward, EdgeType::Regular.mask()).len();
    let post = if regular < 2 {
        None
    } else {
        let (post, statements) = is_choice_statement(ir, head)?;
        if statements.iter().any(|&stat| ir[stat].is_monitor_enter)
            || !check_statement_exceptions(ir, &statements)
        {
            return None;
        }
        post
    };

    Some(new_if(ir, counters, head, regular, post))
}

fn new_if(
    ir: &mut Ir,
    counters: &mut CounterContainer,
    head: StatId,
    mut regular: usize,
    choice_post: Option<StatId>,
) -> StatId {
    let successors = head.get_successor_edges(ir, STATEDGE_DIRECT_ALL);
    let fallthrough = successors[0];
    let jump = successors[1];
    let mut branches = IfStatement::default();
    let mut post = None;

    match regular {
        1 => {
            branches.negated = ir[jump].edge_type == EdgeType::Regular;
            let post_edge = if branches.negated { jump } else { fallthrough };
            post = Some(ir[post_edge].destination);
        }
        2 => {
            let if_stat = ir[jump].destination;
            let else_stat = ir[fallthrough].destination;
            let mask = EdgeType::Regular.mask();
            let if_successors = ir[if_stat].edge_view(Forward, mask).len();
            let else_successors = ir[else_stat].edge_view(Forward, mask).len();
            branches.if_stat = Some(if_stat);
            branches.else_stat = Some(else_stat);

            if ir[if_stat].edge_view(Backward, mask).len() > 1 || if_successors > 1 {
                post = Some(if_stat);
            } else if ir[else_stat].edge_view(Backward, mask).len() > 1
                || else_successors > 1
                || if_successors == 0
            {
                post = Some(else_stat);
            } else if else_successors == 0 {
                post = Some(if_stat);
            }

            if post == Some(if_stat) {
                branches.negated = else_stat != if_stat;
                branches.if_stat = branches.negated.then_some(else_stat);
                branches.else_stat = None;
            } else if post == Some(else_stat) {
                branches.else_stat = None;
            } else {
                post = choice_post;
            }

            if branches.else_stat.is_none() {
                regular = 1;
            }
        }
        _ => {}
    }

    let (if_edge, other_edge) = if branches.negated {
        (fallthrough, jump)
    } else {
        (jump, fallthrough)
    };
    branches.has_else = regular == 2;
    branches.if_edge = Some(if_edge);
    branches.else_edge = branches.has_else.then_some(other_edge);
    let children = [branches.if_stat, branches.else_stat];
    let mut statement = with_head(ir, counters, StatementKind::If(branches), head);
    for child in children.into_iter().flatten() {
        statement.stats.add_with_key(child, ir[child].id);
    }
    let statement = ir.stats.push(statement);

    if regular == 0 {
        head.remove_successor(ir, fallthrough);
        ir[fallthrough].source = statement;
        statement.add_successor(ir, fallthrough);
    } else if regular == 1 {
        head.remove_successor(ir, other_edge);
    }

    ir[statement].post = post.map(|post| if post == head { statement } else { post });
    statement
}

fn detect_catch(
    ir: &mut Ir,
    counters: &mut CounterContainer,
    head: StatId,
    try_loop_fix: bool,
) -> Option<StatId> {
    if ir[head].last_basic_type != LastBasicType::General {
        return None;
    }

    let mut handlers = get_unique_pred_exceptions(ir, head);
    if handlers.is_empty() {
        return None;
    }
    let mut post = regular_successor(ir, head);
    let mut post_count = if post.is_some() { 2 } else { 0 };
    let edges = head.get_successor_edges(ir, EdgeType::Exception.mask());
    for &edge in &edges {
        let target = ir[edge].destination;
        if ir[edge].exceptions.is_none()
            || !handlers.contains(&target)
            || ir[target].last_basic_type != LastBasicType::General
        {
            handlers.shift_remove(&target);
            continue;
        }

        if let Some(target_post) = regular_successor(ir, target) {
            let post = post.get_or_insert(target_post);
            if target_post == *post {
                post_count += 1;
            } else {
                handlers.shift_remove(&target);
            }
        }
    }

    if post_count == 1 || handlers.is_empty() {
        return None;
    }

    let statements: Vec<_> = std::iter::once(head)
        .chain(handlers.iter().copied())
        .collect();
    if statements.iter().any(|&stat| ir[stat].is_monitor_enter)
        || invalid_head_merge(ir, head, try_loop_fix)
        || !check_statement_exceptions(ir, &statements)
    {
        return None;
    }

    let id = counters.get_counter_and_increment(STATEMENT_COUNTER);
    let mut exceptions = Vec::with_capacity(handlers.len());
    let mut vars = Vec::with_capacity(handlers.len());
    let mut stats =
        crate::util::vb_style_collection::VBStyleCollection::with_capacity(handlers.len() + 1);
    stats.add_with_key(head, ir[head].id);
    for edge in edges {
        let handler = ir[edge].destination;
        if handlers.contains(&handler) {
            let types = ir[edge].exceptions.clone().unwrap();
            vars.push(new_exception_var(ir, counters, types[0].clone()));
            exceptions.push(types);
            stats.add_with_key(handler, ir[handler].id);
        }
    }

    let mut statement = Statement::new(
        StatementKind::Catch {
            exceptions,
            vars,
            resources: None,
        },
        id,
    );
    statement.stats = stats;
    statement.first = Some(head);
    statement.post = post;
    Some(ir.stats.push(statement))
}

fn detect_catch_all(
    ir: &mut Ir,
    counters: &mut CounterContainer,
    head: StatId,
    try_loop_fix: bool,
) -> Option<StatId> {
    if ir[head].last_basic_type != LastBasicType::General {
        return None;
    }

    let handlers = get_unique_pred_exceptions(ir, head);
    if handlers.len() != 1 {
        return None;
    }

    for edge in head.get_successor_edges(ir, EdgeType::Exception.mask()) {
        let handler = ir[edge].destination;
        if ir[edge].exceptions.is_some()
            || ir[handler].last_basic_type != LastBasicType::General
            || !handlers.contains(&handler)
            || regular_successor(ir, handler).is_some()
        {
            continue;
        }

        if ir[head].is_monitor_enter
            || ir[handler].is_monitor_enter
            || invalid_head_merge(ir, head, try_loop_fix)
        {
            return None;
        }
        if check_statement_exceptions(ir, &[head, handler]) {
            let id = counters.get_counter_and_increment(STATEMENT_COUNTER);
            let var = new_exception_var(ir, counters, "java/lang/Throwable");
            let mut statement = Statement::new(
                StatementKind::CatchAll {
                    handler: Some(handler),
                    is_finally: false,
                    monitor: None,
                    vars: vec![var],
                },
                id,
            );
            statement.first = Some(head);
            statement.post = regular_successor(ir, head);
            statement.stats.add_with_key(head, ir[head].id);
            statement.stats.add_with_key(handler, ir[handler].id);
            return Some(ir.stats.push(statement));
        }
    }
    None
}

fn new_exception_var(
    ir: &mut Ir,
    counters: &mut CounterContainer,
    class_name: impl Into<ArcStr>,
) -> ExprId {
    Expr::new_variable(
        ir,
        counters,
        VarType::with_value(CodeType::Object, 0, class_name),
    )
}

pub(super) fn on_node_collapse(ir: &mut Ir, counters: &mut CounterContainer, stat: StatId) {
    if matches!(ir[stat].kind, StatementKind::Switch(_)) {
        sort_switch_edges(ir, counters, stat);
    }
}

pub(crate) fn get_simple_copy(
    ir: &mut Ir,
    counters: &mut CounterContainer,
    stat: StatId,
) -> StatId {
    let id = counters.get_counter_and_increment(STATEMENT_COUNTER);
    let kind = match &ir[stat].kind {
        &StatementKind::BasicBlock { block } => {
            let copied = BasicBlock::new(ir, id);
            ir[copied].seq = InstructionSequence::from_collection(
                ir[block]
                    .seq
                    .iter()
                    .map(|instr| Arc::new((**instr).clone())),
            );
            return Statement::new_basic_block(ir, counters, copied);
        }
        StatementKind::Do(_) => StatementKind::Do(DoStatement::default()),
        StatementKind::Switch(_) => StatementKind::Switch(SwitchStatement::default()),
        StatementKind::If(branches) => StatementKind::If(IfStatement {
            has_else: branches.has_else,
            negated: branches.negated,
            ..IfStatement::default()
        }),
        StatementKind::Sequence => StatementKind::Sequence,
        StatementKind::Catch { exceptions, .. } => {
            let exceptions = exceptions.clone();
            let vars = exceptions
                .iter()
                .map(|types| new_exception_var(ir, counters, types[0].clone()))
                .collect();
            StatementKind::Catch {
                exceptions,
                vars,
                resources: None,
            }
        }
        StatementKind::CatchAll {
            is_finally,
            monitor,
            vars,
            ..
        } => {
            let is_finally = *is_finally;
            let has_monitor = monitor.is_some();
            let has_var = !vars.is_empty();
            let monitor =
                has_monitor.then(|| Expr::new_variable(ir, counters, VarType::VARTYPE_INT));
            let vars = has_var.then(|| new_exception_var(ir, counters, "java/lang/Throwable"));
            StatementKind::CatchAll {
                handler: None,
                is_finally,
                monitor,
                vars: vars.into_iter().collect(),
            }
        }
        _ => panic!("Statement cannot be copied by the irreducible graph splitter"),
    };
    ir.stats.push(Statement::new(kind, id))
}

pub(crate) fn init_simple_copy(ir: &mut Ir, counters: &mut CounterContainer, stat: StatId) {
    let Some(&first) = ir[stat].stats.first() else {
        return;
    };
    ir[stat].first = Some(first);
    match ir[stat].kind {
        StatementKind::If(mut branches) => {
            let successors = first.get_successor_edges(ir, STATEDGE_DIRECT_ALL);
            branches.if_edge =
                Some(successors[usize::from(branches.has_else && !branches.negated)]);
            branches.else_edge = branches
                .has_else
                .then(|| successors[usize::from(branches.negated)]);
            branches.if_stat = ir[stat].stats.get(1).copied();
            branches.else_stat = branches.has_else.then(|| ir[stat].stats[2]);
            ir[stat].kind = StatementKind::If(branches);
        }
        StatementKind::CatchAll { .. } => {
            let handler_stat = ir[stat].stats[1];
            let StatementKind::CatchAll { handler, .. } = &mut ir[stat].kind else {
                unreachable!()
            };
            *handler = Some(handler_stat);
        }
        StatementKind::Switch(_) => {
            let default = first_direct_edge(ir, first);
            let StatementKind::Switch(switch) = &mut ir[stat].kind else {
                unreachable!()
            };
            switch.default_edge = default;
            sort_switch_edges(ir, counters, stat);
        }
        _ => {}
    }
}

pub(super) fn replace_child(ir: &mut Ir, owner: StatId, old: StatId, new: StatId) {
    if let StatementKind::If(mut branches) = ir[owner].kind {
        if branches.if_stat == Some(old) {
            branches.if_stat = Some(new);
        }
        if branches.else_stat == Some(old) {
            branches.else_stat = Some(new);
        }
        let first = ir[owner].first.unwrap();
        let successors = ir[first].edge_view(Forward, STATEDGE_DIRECT_ALL);
        let (if_edge, else_edge) = if !branches.has_else {
            (successors[0], None)
        } else if Some(ir[successors[0]].destination) == branches.if_stat {
            (successors[0], Some(successors[1]))
        } else {
            (successors[1], Some(successors[0]))
        };
        branches.if_edge = Some(if_edge);
        branches.else_edge = else_edge;
        ir[owner].kind = StatementKind::If(branches);
    } else if let StatementKind::Switch(switch) = &mut ir[owner].kind {
        let mut replaced = false;
        for case in &mut switch.cases {
            if case.statement == old {
                case.statement = new;
                replaced = true;
            }
        }
        assert!(
            replaced,
            "Replaced statement without replacing any switch case"
        );
    } else if let StatementKind::CatchAll { handler, .. } = &mut ir[owner].kind
        && *handler == Some(old)
    {
        *handler = Some(new);
    } else if let StatementKind::Synchronized { body, .. } = &mut ir[owner].kind
        && *body == old
    {
        *body = new;
    }
}
