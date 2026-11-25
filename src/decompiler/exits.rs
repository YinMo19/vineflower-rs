// Copyright 2000-2020 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Integrate a copied return or throw at the source of a break.

use std::io;

use crate::decompiler::decompose::finish::condense_sequences;
use crate::decompiler::exps::{Expr, ExprKind, FunctionType};
use crate::decompiler::ir::{EdgeId, ExprId, Ir, StatId};
use crate::decompiler::labels::is_direct_path;
use crate::decompiler::stats::stat_edge::{EdgeType, StatEdge};
use crate::decompiler::stats::{
    IfStatement, STATEDGE_ALL, STATEDGE_DIRECT_ALL, Statement, StatementKind,
};
use crate::engine::{Cx, counter_container::CounterContainer};

pub(crate) fn condense(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    root: StatId,
) -> io::Result<bool> {
    let changed = integrate(cx, counters, root)?;
    if changed {
        clean_unreachable(&mut cx.ir, root)?;
        condense_sequences(cx, counters, root);
    }
    Ok(changed)
}

fn integrate(cx: &mut Cx, counters: &mut CounterContainer, stat: StatId) -> io::Result<bool> {
    let mut changed = false;
    if cx.ir[stat].exprents.is_none() {
        loop {
            let mut child_changed = false;
            for index in 0..cx.ir[stat].stats.len() {
                let child = cx.ir[stat].stats[index];
                if integrate(cx, counters, child)? {
                    child_changed = true;
                    changed = true;
                    break;
                }
            }
            if !child_changed {
                break;
            }
        }
        if let Some(candidate) = ConditionalExit::find(&cx.ir, stat) {
            candidate.install(cx, counters, stat)?;
            changed = true;
        }
    }
    if let Some(candidate) = TailExit::find(&cx.ir, stat) {
        candidate.install(cx, counters, stat)?;
        changed = true;
    }
    Ok(changed)
}

fn clean_unreachable(ir: &mut Ir, stat: StatId) -> io::Result<()> {
    loop {
        let mut found = false;
        for index in 0..ir[stat].stats.len() {
            let child = ir[stat].stats[index];
            clean_unreachable(ir, child)?;
            if let Some(last) = unreachable_tail(ir, child) {
                let list = ir[last]
                    .exprents
                    .ok_or_else(|| invalid("Unreachable exit block has no expressions"))?;
                ir[list].clear();
                let id = ir[last].id;
                ir[child].stats.remove_with_key(&id);
                for edge in last.get_successor_edges(ir, STATEDGE_ALL) {
                    edge.remove(ir);
                }
                for edge in last.get_predecessor_edges(ir, STATEDGE_ALL) {
                    edge.remove(ir);
                }
                found = true;
                break;
            }
        }
        if !found {
            return Ok(());
        }
    }
}

fn unreachable_tail(ir: &Ir, stat: StatId) -> Option<StatId> {
    if !matches!(ir[stat].kind, StatementKind::Sequence) {
        return None;
    }
    let [.., preceding, last] = &ir[stat].stats[..] else {
        return None;
    };
    if ir[*preceding].has_basic_succ_edge()
        || last
            .get_predecessor_edges(ir, STATEDGE_DIRECT_ALL)
            .iter()
            .any(|&edge| ir[edge].source != *preceding)
    {
        return None;
    }
    Some(*last)
}

struct ConditionalExit {
    if_edge: EdgeId,
    exit: StatId,
    alternative: Option<EdgeId>,
}

impl ConditionalExit {
    fn find(ir: &Ir, stat: StatId) -> Option<Self> {
        let StatementKind::If(branch) = ir[stat].kind else {
            return None;
        };
        if branch.if_stat.is_some() {
            return None;
        }
        let if_edge = branch.if_edge?;
        if let Some(exit) = exit_edge(ir, if_edge) {
            return Some(Self {
                if_edge,
                exit,
                alternative: None,
            });
        }
        let alternative = first_edge(ir, stat, EdgeType::Break).or_else(|| {
            let adjacent = ir[first_edge(ir, stat, EdgeType::Regular)?].destination;
            first_edge(ir, adjacent, EdgeType::Break)
        })?;
        let exit = if_break_exit(ir, stat, alternative)?;
        Some(Self {
            if_edge,
            exit,
            alternative: Some(alternative),
        })
    }

    fn install(self, cx: &mut Cx, counters: &mut CounterContainer, stat: StatId) -> io::Result<()> {
        let block = copy_exit_block(cx, counters, self.exit);
        // Replacing the original exit block can move this edge to a new source.
        let old_exit = cx.ir[self.exit]
            .first_successor()
            .ok_or_else(|| invalid("Conditional exit has no successor"))?;
        if let Some(alternative) = self.alternative {
            self.repair_conditional_switch(cx, counters, stat, block, alternative)?;
        }
        let ir = &mut cx.ir;
        let head = ir[stat].first.expect("If statement has no head");
        let taken = StatEdge::new(ir, EdgeType::Regular, head, block, None);
        head.remove_successor(ir, self.if_edge);
        head.add_successor(ir, taken);
        let StatementKind::If(branch) = &mut ir[stat].kind else {
            unreachable!();
        };
        branch.if_edge = Some(taken);
        branch.if_stat = Some(block);
        let id = ir[block].id;
        ir[stat].stats.add_with_key(block, id);
        ir[block].parent = Some(stat);
        attach_exit_edge(ir, block, old_exit)
    }

    fn repair_conditional_switch(
        &self,
        cx: &mut Cx,
        counters: &mut CounterContainer,
        stat: StatId,
        block: StatId,
        alternative: EdgeId,
    ) -> io::Result<()> {
        let parent = cx.ir[stat].parent.expect("Conditional exit has no parent");
        let in_sequence = matches!(cx.ir[parent].kind, StatementKind::Sequence);
        let source = cx.ir[alternative].source;
        if in_sequence && cx.ir[source].exprents.is_some() {
            let prefix = copy_expressions(cx, counters, source);
            let list = cx.ir[block].exprents.unwrap();
            cx.ir[list].splice(..0, prefix);
        }
        let switch = if in_sequence {
            cx.ir[parent].parent
        } else {
            Some(parent)
        };
        let Some(switch) = switch else { return Ok(()) };
        let StatementKind::Switch(switch) = &cx.ir[switch].kind else {
            return Ok(());
        };
        let default = switch.default_edge;
        let StatementKind::If(branch) = cx.ir[stat].kind else {
            unreachable!();
        };
        let header = if_header(&cx.ir, branch);
        let ExprKind::If { condition } = cx.ir[header].kind else {
            unreachable!("If header must be an IfExprent");
        };
        let ExprKind::Function {
            op: FunctionType::BoolNot,
            operands,
            ..
        } = &cx.ir[condition].kind
        else {
            return Ok(());
        };
        cx.ir[header].kind = ExprKind::If {
            condition: operands[0],
        };

        let ir = &mut cx.ir;
        let Some(default) = default else {
            return Ok(());
        };
        let successor = ir[ir[default].destination]
            .first_successor()
            .ok_or_else(|| invalid("Switch default edge has no successor"))?;
        let default = ir[successor].destination;
        if ir[self.if_edge].destination == default {
            if in_sequence {
                let regular = first_edge(ir, stat, EdgeType::Regular)
                    .ok_or_else(|| invalid("Inverted switch condition has no regular successor"))?;
                regular.change_source(ir, parent);
                let source = ir[alternative].source;
                let empty = Statement::new_empty_basic_block(ir, counters);
                source.replace_with(ir, empty);
                let destination = ir[alternative].destination;
                let empty = Statement::new_empty_basic_block(ir, counters);
                destination.replace_with(ir, empty);
            } else {
                stat.remove_successor(ir, alternative);
            }
            let edge = StatEdge::new(ir, EdgeType::Break, stat, default, ir[self.if_edge].closure);
            stat.add_successor(ir, edge);
        }
        Ok(())
    }
}

struct TailExit {
    parent: StatId,
    jump: EdgeId,
    exit: StatId,
}

impl TailExit {
    fn find(ir: &Ir, stat: StatId) -> Option<Self> {
        let &[jump] = ir[stat].all_successors() else {
            return None;
        };
        if ir[jump].edge_type != EdgeType::Break || !ir[stat].label_edges.is_empty() {
            return None;
        }
        let parent = ir[stat].parent?;
        if ir[parent].first == Some(stat)
            && matches!(
                ir[parent].kind,
                StatementKind::If(_) | StatementKind::Switch(_)
            )
        {
            return None;
        }
        Some(Self {
            parent,
            jump,
            exit: exit_edge(ir, jump)?,
        })
    }

    fn install(self, cx: &mut Cx, counters: &mut CounterContainer, stat: StatId) -> io::Result<()> {
        self.jump.remove(&mut cx.ir);
        let block = copy_exit_block(cx, counters, self.exit);
        let ir = &mut cx.ir;
        let old_exit = ir[self.exit]
            .first_successor()
            .ok_or_else(|| invalid("Copied exit has no successor"))?;
        attach_exit_edge(ir, block, old_exit)?;
        let sequence = Statement::new_sequence(ir, counters, &[stat, block]);
        sequence.set_all_parent(ir);
        self.parent.replace_statement(ir, stat, sequence);

        for edge in sequence.get_predecessor_edges(ir, EdgeType::Continue.mask()) {
            edge.change_destination(ir, stat);
            stat.add_labeled_edge(ir, edge);
        }
        let edge = StatEdge::new(ir, EdgeType::Regular, stat, block, None);
        stat.add_successor(ir, edge);

        for edge in self.exit.get_predecessor_edges(ir, STATEDGE_ALL) {
            let source = ir[edge].source;
            if !ir[edge].explicit
                && stat.contains_statement_strict(ir, source)
                && ir[source]
                    .parent
                    .is_some_and(|parent| is_direct_path(ir, parent, block))
            {
                edge.change_destination(ir, block);
                if ir[edge]
                    .closure
                    .is_none_or(|closure| !stat.contains_statement_strict(ir, closure))
                {
                    stat.add_labeled_edge(ir, edge);
                }
            }
        }
        Ok(())
    }
}

fn exit_edge(ir: &Ir, edge: EdgeId) -> Option<StatId> {
    let dest = inlineable_break(ir, edge)?;
    if accepted_exit(ir, edge, dest) && (ir[edge].labeled || is_only_edge(ir, edge)) {
        Some(dest)
    } else {
        None
    }
}

fn if_break_exit(ir: &Ir, stat: StatId, edge: EdgeId) -> Option<StatId> {
    let head = stat.get_basic_head(ir);
    if !ir[head].exprents.is_some_and(|list| ir[list].is_empty()) {
        return None;
    }
    let dest = inlineable_break(ir, edge)?;
    if !ir[edge].labeled && !is_only_edge(ir, edge) {
        let parent = ir[stat].parent?;
        if Some(parent) != ir[edge].closure
            || ir[parent]
                .first_successor()
                .is_none_or(|successor| ir[successor].destination != dest)
        {
            return None;
        }
    }
    accepted_exit(ir, edge, dest).then_some(dest)
}

fn inlineable_break(ir: &Ir, edge: EdgeId) -> Option<StatId> {
    let edge = &ir[edge];
    (edge.edge_type == EdgeType::Break
        && edge.explicit
        && edge.can_inline
        && matches!(ir[edge.destination].kind, StatementKind::BasicBlock { .. }))
    .then_some(edge.destination)
}

fn accepted_exit(ir: &Ir, edge: EdgeId, dest: StatId) -> bool {
    let phantom = std::iter::successors(ir[edge].closure, |&parent| ir[parent].parent)
        .any(|parent| ir[parent].phantom && matches!(ir[parent].kind, StatementKind::Switch(_)));
    !phantom
        && ir[dest].exprents.is_some_and(|list| {
            matches!(ir[list].as_slice(), &[expr] if matches!(ir[expr].kind, ExprKind::Exit { .. }))
        })
}

fn is_only_edge(ir: &Ir, edge: EdgeId) -> bool {
    ir[edge]
        .destination
        .get_predecessor_edges(ir, STATEDGE_ALL)
        .into_iter()
        .all(|other| {
            other == edge
                || ir[other].edge_type == EdgeType::Regular
                    && !ir[ir[other].source].has_basic_succ_edge()
        })
}

fn first_edge(ir: &Ir, stat: StatId, ty: EdgeType) -> Option<EdgeId> {
    stat.get_successor_edges(ir, ty.mask()).first().copied()
}

fn if_header(ir: &Ir, branch: IfStatement) -> ExprId {
    ir[branch
        .head_exprents
        .expect("If statement has no expression header")][0]
}

fn copy_exit_block(cx: &mut Cx, counters: &mut CounterContainer, source: StatId) -> StatId {
    let block = Statement::new_empty_basic_block(&mut cx.ir, counters);
    let copied = copy_expressions(cx, counters, source);
    let list = cx.ir[block].exprents.unwrap();
    cx.ir[list] = copied;
    block
}

fn copy_expressions(cx: &mut Cx, counters: &mut CounterContainer, source: StatId) -> Vec<ExprId> {
    let list = cx.ir[source]
        .exprents
        .expect("Exit block has no expressions");
    let originals = cx.ir[list].clone();
    originals
        .into_iter()
        .map(|expr| Expr::copy(cx, counters, expr))
        .collect()
}

fn attach_exit_edge(ir: &mut Ir, source: StatId, original: EdgeId) -> io::Result<()> {
    let edge = StatEdge::new(ir, EdgeType::Break, source, ir[original].destination, None);
    source.add_successor(ir, edge);
    let closure = ir[original]
        .closure
        .ok_or_else(|| invalid("Exit edge has no closure"))?;
    closure.add_labeled_edge(ir, edge);
    Ok(())
}

fn invalid(message: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}
