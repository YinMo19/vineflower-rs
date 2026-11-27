//! LoopExtractHelper: move an entry or exit conditional's body.

use crate::decompiler::decompose::finish::condense_sequences;
use crate::decompiler::exps::FunctionType;
use crate::decompiler::ir::{EdgeId, Expr, ExprKind, Ir, StatId};
use crate::decompiler::stats::stat_edge::{EdgeType, StatEdge};
use crate::decompiler::stats::{LoopType, Statement, StatementKind};
use crate::engine::{Cx, counter_container::CounterContainer};

pub(crate) fn extract(cx: &mut Cx, counters: &mut CounterContainer, root: StatId) -> bool {
    let changed = extract_recursive(&mut cx.ir, counters, root) != Extraction::Unchanged;
    if changed {
        condense_sequences(cx, counters, root);
    }
    changed
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Extraction {
    Unchanged,
    Descendant,
    Loop,
}

fn extract_recursive(ir: &mut Ir, counters: &mut CounterContainer, stat: StatId) -> Extraction {
    let mut result = Extraction::Unchanged;
    'rescan: loop {
        // Extracting a child may replace it in this parent's collection.
        let children = ir[stat].stats.to_vec();
        for child in children {
            match extract_recursive(ir, counters, child) {
                Extraction::Unchanged => {}
                Extraction::Descendant => result = Extraction::Descendant,
                Extraction::Loop => {
                    result = Extraction::Descendant;
                    continue 'rescan;
                }
            }
        }
        break;
    }

    if is_infinite_loop(ir, stat) && extract_loop(ir, counters, stat) {
        return Extraction::Loop;
    }
    result
}

fn is_infinite_loop(ir: &Ir, stat: StatId) -> bool {
    matches!(ir[stat].kind, StatementKind::Do(header) if header.ty == LoopType::Infinite)
}

fn extract_loop(ir: &mut Ir, counters: &mut CounterContainer, loop_stat: StatId) -> bool {
    let mut breaks = Vec::new();
    for &edge in &ir[loop_stat].label_edges {
        let edge = &ir[edge];
        if edge.edge_type == EdgeType::Continue
            || matches!(ir[edge.destination].kind, StatementKind::DummyExit { .. })
        {
            continue;
        }
        if edge.edge_type != EdgeType::Break
            || !is_external(ir, loop_stat, edge.source, edge.source)
        {
            return false;
        }
        breaks.push(edge.source);
    }

    if !breaks.is_empty()
        && ir[ir[loop_stat].parent.unwrap()].stats.last().copied() != Some(loop_stat)
    {
        return false;
    }

    let mut first = ir[loop_stat].first.unwrap();
    while matches!(ir[first].kind, StatementKind::Sequence) {
        first = ir[first].first.unwrap();
    }
    extract_first_if(ir, counters, loop_stat, first, &breaks)
        || extract_last_if(ir, counters, loop_stat, first, &breaks)
}

fn extract_first_if(
    ir: &mut Ir,
    counters: &mut CounterContainer,
    loop_stat: StatId,
    first: StatId,
    breaks: &[StatId],
) -> bool {
    let StatementKind::If(branch) = ir[first].kind else {
        return false;
    };
    let head = ir[first].first.unwrap();
    if !ir[ir[head].exprents.unwrap()].is_empty() || branch.has_else {
        return false;
    }
    let Some(target) = branch.if_stat else {
        return false;
    };

    if is_external(ir, loop_stat, target, target) {
        if !breaks.iter().all(|&source| contains(ir, target, source)) {
            return false;
        }
        extract_if_block(
            ir,
            counters,
            loop_stat,
            first,
            target,
            branch.if_edge.unwrap(),
        );
        return true;
    }

    if ir[loop_stat].stats.len() != 1 {
        return false;
    }
    let continue_mask = EdgeType::Continue.mask();
    let mut continues = target.get_successor_edges(ir, continue_mask);
    if matches!(ir[target].kind, StatementKind::Sequence) {
        let last = *ir[target].stats.last().unwrap();
        continues.extend(last.get_successor_edges(ir, continue_mask));
    }
    if !matches!(continues.as_slice(), [edge] if ir[*edge].destination == loop_stat) {
        return false;
    }

    let regular = EdgeType::Regular.mask();
    let Some(out) = std::iter::successors(Some(loop_stat), |&stat| ir[stat].parent)
        .find_map(|stat| stat.get_successor_edges(ir, regular).first().copied())
    else {
        return false;
    };
    let destination = ir[out].destination;
    extract_if_block_into_loop(ir, counters, loop_stat, first, target, destination);
    true
}

fn extract_last_if(
    ir: &mut Ir,
    counters: &mut CounterContainer,
    loop_stat: StatId,
    first: StatId,
    breaks: &[StatId],
) -> bool {
    let mut last = ir[loop_stat].first.unwrap();
    while matches!(ir[last].kind, StatementKind::Sequence) {
        last = *ir[last].stats.last().unwrap();
    }
    let StatementKind::If(branch) = ir[last].kind else {
        return false;
    };
    let Some(target) = branch.if_stat.filter(|_| !branch.has_else) else {
        return false;
    };
    let Some(other) = ir[last].first_successor() else {
        return false;
    };
    if ir[other].edge_type != EdgeType::Continue || ir[other].closure != Some(loop_stat) {
        return false;
    }
    if loop_stat
        .get_predecessor_edges(ir, EdgeType::Continue.mask())
        .iter()
        .any(|&edge| ir[edge].source != last)
        || !is_external(ir, loop_stat, target, target)
        || is_infinite_loop(ir, first)
        || !breaks.iter().all(|&source| contains(ir, target, source))
    {
        return false;
    }

    extract_if_block(
        ir,
        counters,
        loop_stat,
        last,
        target,
        branch.if_edge.unwrap(),
    );
    true
}

fn contains(ir: &Ir, stat: StatId, target: StatId) -> bool {
    stat == target || stat.contains_statement_strict(ir, target)
}

fn is_external(ir: &Ir, loop_stat: StatId, block: StatId, stat: StatId) -> bool {
    ir[stat].all_successors().iter().all(|&edge| {
        let destination = ir[edge].destination;
        !contains(ir, loop_stat, destination) || contains(ir, block, destination)
    }) && ir[stat]
        .stats
        .iter()
        .all(|&child| is_external(ir, loop_stat, block, child))
}

fn make_if_break(ir: &mut Ir, loop_stat: StatId, if_stat: StatId, target: StatId, edge: EdgeId) {
    let StatementKind::If(branch) = &mut ir[if_stat].kind else {
        unreachable!();
    };
    branch.if_stat = None;
    edge.change_type(ir, EdgeType::Break);
    ir[edge].closure = Some(loop_stat);
    let target_id = ir[target].id;
    ir[if_stat].stats.remove_with_key(&target_id);
}

fn extract_if_block(
    ir: &mut Ir,
    counters: &mut CounterContainer,
    loop_stat: StatId,
    if_stat: StatId,
    target: StatId,
    edge: EdgeId,
) {
    make_if_break(ir, loop_stat, if_stat, target, edge);
    loop_stat.add_labeled_edge(ir, edge);

    let sequence = Statement::new_sequence(ir, counters, &[loop_stat, target]);
    loop_stat.replace_with(ir, sequence);
    sequence.set_all_parent(ir);
    let successor = StatEdge::new(ir, EdgeType::Regular, loop_stat, target, None);
    loop_stat.add_successor(ir, successor);

    let labels: Vec<_> = ir[sequence].label_edges.iter().copied().collect();
    for label in labels {
        if ir[label].edge_type == EdgeType::Continue || label == edge {
            loop_stat.add_labeled_edge(ir, label);
        }
    }
    for edge in sequence.get_predecessor_edges(ir, EdgeType::Continue.mask()) {
        if loop_stat.contains_statement_strict(ir, ir[edge].source) {
            edge.change_destination(ir, loop_stat);
        }
    }
    if let [edge] = target
        .get_predecessor_edges(ir, EdgeType::Break.mask())
        .as_slice()
    {
        ir[*edge].can_inline = false;
    }
}

fn extract_if_block_into_loop(
    ir: &mut Ir,
    counters: &mut CounterContainer,
    loop_stat: StatId,
    if_stat: StatId,
    target: StatId,
    destination: StatId,
) {
    let StatementKind::If(branch) = ir[if_stat].kind else {
        unreachable!();
    };
    let edge = branch.if_edge.unwrap();
    let old_destination = ir[edge].destination;
    old_destination.remove_predecessor(ir, edge);
    // Retyping restores only the Break index on the old destination.
    // Java leaves that entry there when it registers the new destination.
    make_if_break(ir, loop_stat, if_stat, target, edge);
    ir[edge].destination = destination;
    destination.add_predecessor(ir, edge);
    loop_stat.add_labeled_edge(ir, edge);

    let sequence = Statement::new_sequence(ir, counters, &[if_stat, target]);
    if_stat.replace_with(ir, sequence);
    sequence.set_all_parent(ir);
    let successor = StatEdge::new(ir, EdgeType::Regular, if_stat, target, None);
    if_stat.add_successor(ir, successor);

    let header = ir[branch.head_exprents.unwrap()][0];
    let ExprKind::If { condition } = ir[header].kind else {
        unreachable!("If statement header must be an IfExprent");
    };
    let condition = Expr::function(ir, counters, FunctionType::BoolNot, vec![condition], None);
    ir[header].kind = ExprKind::If { condition };
}
