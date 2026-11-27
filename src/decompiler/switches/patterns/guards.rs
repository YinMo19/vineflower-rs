//! Remove restart-index assignments and recover guarded case conditions.

use std::collections::VecDeque;
use std::io;

use super::{identify_record, int_constant, invalid, switch};
use crate::decompiler::exps::{Expr, ExprKind, FunctionType};
use crate::decompiler::ir::{EdgeId, ExprId, Ir, StatId};
use crate::decompiler::stats::stat_edge::{EdgeType, StatEdge};
use crate::decompiler::stats::{IfStatement, STATEDGE_ALL, Statement, StatementKind};
use crate::engine::{Cx, counter_container::CounterContainer};
use crate::types::TypeFamily;

pub(super) struct Guards {
    pub guarded: bool,
    /// Case-value lists stay in place until all guard references have been
    /// examined. Their corresponding case positions keep the association.
    pub entries: Vec<Option<ExprId>>,
}

#[derive(Clone, Copy)]
struct Reference {
    stat: StatId,
    expr: ExprId,
}

pub(super) fn recover(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    root: StatId,
    stat: StatId,
    restart: ExprId,
) -> io::Result<Option<Guards>> {
    let mut result = Guards {
        guarded: true,
        entries: vec![None; switch(&cx.ir, stat).cases.len()],
    };
    let refs = if Expr::variable(&cx.ir, restart).is_some() {
        references(&cx.ir, root, restart)
    } else {
        Vec::new()
    };
    let Some((&initial, rest)) = refs.split_first() else {
        return Err(invalid("Pattern switch has no restart-index reference"));
    };
    let Some((_, value)) = cx.ir[initial.expr].as_assignment() else {
        return Ok(None);
    };

    if rest.is_empty() {
        remove_reference(cx, initial);
        result.guarded = false;
        return Ok(Some(result));
    }
    if !matches!(&cx.ir[value].kind, ExprKind::Constant { var_type, .. }
        if var_type.type_family == TypeFamily::Integer)
        || int_constant(&cx.ir, value) != Some(0)
    {
        return Ok(None);
    }

    let mut eliminable = true;
    for &reference in rest {
        eliminable &= eliminate(cx, counters, stat, &mut result.entries, reference, true)?;
    }
    if !eliminable {
        return Ok(None);
    }
    remove_reference(cx, initial);
    for &reference in rest {
        eliminate(cx, counters, stat, &mut result.entries, reference, false)?;
    }
    Ok(Some(result))
}

fn references(ir: &Ir, root: StatId, var: ExprId) -> Vec<Reference> {
    let mut refs = Vec::new();
    let mut pending = VecDeque::from([root]);
    while let Some(stat) = pending.pop_front() {
        pending.extend(ir[stat].stats.iter().copied());
        if let Some(list) = ir[stat].exprents {
            for &expr in &ir[list] {
                if Expr::is_var_referenced(ir, var, expr, &[]) {
                    refs.push(Reference { stat, expr });
                }
            }
        }
    }
    refs
}

fn remove_reference(cx: &mut Cx, reference: Reference) {
    let list = cx.ir[reference.stat]
        .exprents
        .expect("Restart-index block has no expressions");
    if let Some(index) = cx.ir[list]
        .iter()
        .position(|&expr| Expr::equals(cx, reference.expr, expr))
    {
        cx.ir[list].remove(index);
    }
}

fn eliminate(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    stat: StatId,
    guards: &mut [Option<ExprId>],
    reference: Reference,
    simulate: bool,
) -> io::Result<bool> {
    if cx.ir[reference.expr].as_assignment().is_none() {
        return Ok(false);
    }
    let assign_stat = reference.stat;
    if let Some(index) = enclosing_case(&cx.ir, stat, assign_stat) {
        let case = switch(&cx.ir, stat).cases[index].statement;
        if let Some(pattern) = identify_record(cx, counters, stat, case, simulate)? {
            if !simulate {
                guards[index] = Some(pattern);
            }
            return Ok(true);
        }
    }

    let ir = &cx.ir;
    if assign_stat.get_predecessor_edges(ir, STATEDGE_ALL).len() > 1 {
        return Ok(false);
    }
    let Some(mut parent) = ir[assign_stat].parent else {
        return Ok(false);
    };
    let mut invert = true;
    if matches!(ir[parent].kind, StatementKind::Sequence)
        && let [guard, tail] = &ir[parent].stats[..]
        && *tail == assign_stat
    {
        parent = *guard;
        invert = false;
    }

    if let Some(guard) = ordinary_guard(ir, stat, assign_stat, parent, invert)? {
        if Some(ir[guard.restart_edge].destination) != ir[stat].parent {
            return Ok(false);
        }
        let condition = if_condition(ir, guard.branch);
        let Some(index) = enclosing_case(ir, stat, assign_stat) else {
            return Ok(false);
        };
        if !simulate {
            guards[index] = Some(guard.extract(cx, counters, parent, condition)?);
        }
        return Ok(true);
    }
    if parent == stat
        && let Some(index) = enclosing_case(ir, stat, assign_stat)
    {
        if !simulate {
            guards[index] = Some(Expr::new_int_constant(&mut cx.ir, counters, 0, true));
            replace_false_guard(&mut cx.ir, counters, stat, assign_stat)?;
        }
        return Ok(true);
    }
    Ok(false)
}

struct Guard {
    sequence: StatId,
    body: StatId,
    branch: IfStatement,
    restart_edge: EdgeId,
    invert: bool,
}

fn ordinary_guard(
    ir: &Ir,
    stat: StatId,
    assignment: StatId,
    parent: StatId,
    invert: bool,
) -> io::Result<Option<Guard>> {
    let StatementKind::If(branch) = ir[parent].kind else {
        return Ok(None);
    };
    let Some(body) = branch.if_stat else {
        return Ok(None);
    };
    let Some(sequence) = ir[parent].parent else {
        return Ok(None);
    };
    if !matches!(ir[assignment].kind, StatementKind::BasicBlock { .. })
        || ir[assignment]
            .exprents
            .is_none_or(|list| ir[list].len() != 1)
        || branch.has_else
        || !matches!(ir[sequence].kind, StatementKind::Sequence)
        || ir[sequence].parent != Some(stat)
    {
        return Ok(None);
    }
    let restart_edge = assignment
        .get_successor_edges(ir, EdgeType::Continue.mask())
        .first()
        .copied()
        .ok_or_else(|| invalid("Pattern switch guard has no restart edge"))?;
    Ok(Some(Guard {
        sequence,
        body,
        branch,
        restart_edge,
        invert,
    }))
}

impl Guard {
    fn extract(
        self,
        cx: &mut Cx,
        counters: &mut CounterContainer,
        guard_if: StatId,
        condition: ExprId,
    ) -> io::Result<ExprId> {
        let ir = &mut cx.ir;
        let head = ir[guard_if].stats[0];
        let guard_exprs = ir[head]
            .exprents
            .expect("Pattern guard has no head expressions");
        let carry = ir[guard_exprs].first().copied();

        self.restart_edge.remove(ir);
        ir[self.sequence].stats.remove(0);
        let (condition, body) = if self.invert {
            let offsets = ir[condition].bytecode.clone();
            let condition = Expr::function(
                ir,
                counters,
                FunctionType::BoolNot,
                vec![condition],
                offsets,
            );
            let body = ir[self.sequence]
                .stats
                .first()
                .copied()
                .ok_or_else(|| invalid("Pattern switch guard has no following body"))?;
            (condition, body)
        } else {
            ir[self.sequence].stats.remove(0);
            ir[self.sequence].stats.push(self.body);
            (condition, self.body)
        };
        ir[self.sequence].first = Some(body);
        for edge in body.get_predecessor_edges(ir, STATEDGE_ALL) {
            edge.remove(ir);
        }
        let body_head = body.get_basic_head(ir);
        let body_exprs = ir[body_head]
            .exprents
            .expect("Pattern case has no body expressions");
        if let Some(carry) = carry {
            ir[body_exprs].insert(0, carry);
        }
        Ok(condition)
    }
}

fn replace_false_guard(
    ir: &mut Ir,
    counters: &mut CounterContainer,
    stat: StatId,
    assignment: StatId,
) -> io::Result<()> {
    let replacement = Statement::new_empty_basic_block(ir, counters);
    assignment.replace_with(ir, replacement);
    let removed = ir[replacement]
        .first_successor()
        .ok_or_else(|| invalid("False switch guard has no succeeding edge"))?;
    removed.remove(ir);

    let parent = ir[stat].parent.expect("Guarded switch has no parent");
    let mut destinations = ir[parent].label_edges.iter().filter_map(|&edge| {
        (ir[edge].edge_type == EdgeType::Break).then_some(ir[edge].destination)
    });
    if let Some(target) = destinations.next()
        && destinations.all(|destination| destination == target)
    {
        let edge = StatEdge::new(ir, EdgeType::Break, replacement, target, Some(parent));
        replacement.add_successor(ir, edge);
    }
    Ok(())
}

fn enclosing_case(ir: &Ir, stat: StatId, nested: StatId) -> Option<usize> {
    switch(ir, stat).cases.iter().position(|case| {
        case.statement == nested || case.statement.contains_statement_strict(ir, nested)
    })
}

fn if_condition(ir: &Ir, branch: IfStatement) -> ExprId {
    let head = branch
        .head_exprents
        .expect("Pattern guard if has no header");
    let ExprKind::If { condition } = ir[ir[head][0]].kind else {
        unreachable!("Expected an IfExprent");
    };
    condition
}
