// Copyright 2000-2020 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Graph predicates from `modules.decompiler.DecHelper`.

use indexmap::IndexSet;

use crate::decompiler::ir::{Ir, StatId};
use crate::decompiler::stats::EdgeDirection::{Backward, Forward};
use crate::decompiler::stats::stat_edge::EdgeType;
use crate::decompiler::stats::{LastBasicType, STATEDGE_DIRECT_ALL, StatementKind};

pub(super) fn check_statement_exceptions(ir: &Ir, statements: &[StatId]) -> bool {
    let all: IndexSet<_> = statements.iter().copied().collect();
    let mut handlers = IndexSet::new();
    let mut intersection: Option<IndexSet<_>> = None;
    for &stat in statements {
        let successors: IndexSet<_> = stat
            .get_neighbours(ir, EdgeType::Exception.mask(), Forward)
            .into_iter()
            .collect();
        if let Some(common) = &mut intersection {
            handlers.extend(common.symmetric_difference(&successors).copied());
            common.retain(|handler| successors.contains(handler));
        } else {
            intersection = Some(successors);
        }
    }

    for &handler in &handlers {
        if !all.contains(&handler)
            || handler
                .get_neighbours(ir, EdgeType::Exception.mask(), Backward)
                .iter()
                .any(|pred| !all.contains(pred))
        {
            return false;
        }
    }

    // A handler outside the partial ranges previously found can only be the head.
    statements.iter().skip(1).all(|&stat| {
        ir[stat]
            .edge_view(Backward, EdgeType::Exception.mask())
            .is_empty()
            || handlers.contains(&stat)
    })
}

pub(super) fn is_choice_statement(ir: &Ir, head: StatId) -> Option<(Option<StatId>, Vec<StatId>)> {
    let regular = EdgeType::Regular.mask();
    // The upstream set has no specified iteration order. Keep the successor
    // order of the graph when choosing which candidate to inspect next.
    let mut destinations: IndexSet<_> = head
        .get_neighbours(ir, regular, Forward)
        .into_iter()
        .collect();
    if destinations.contains(&head) {
        return None;
    }

    let mut post = None;
    let mut statements = Vec::with_capacity(destinations.len() + 1);
    'retry: loop {
        statements.clear();
        if let Some(post) = post {
            destinations.shift_remove(&post);
        }

        for &stat in &destinations {
            if ir[stat].last_basic_type != LastBasicType::General {
                if post.replace(stat).is_some() {
                    return None;
                }
                continue 'retry;
            }

            let predecessors = choice_predecessors(ir, stat, head);
            if predecessors.contains(&stat) {
                return None;
            }
            if predecessors.len() > 1 || !predecessors.is_subset(&destinations) {
                if post.replace(stat).is_some() {
                    return None;
                }
                continue 'retry;
            }

            if let Some(&predecessor) = predecessors.first() {
                let mut predecessor = predecessor;
                while statements.contains(&predecessor) {
                    let previous = choice_predecessors(ir, predecessor, head);
                    let Some(&previous) = previous.first() else {
                        break;
                    };
                    predecessor = previous;
                    if predecessor == stat {
                        return None;
                    }
                }
            }

            let direct = ir[stat].edge_view(Forward, STATEDGE_DIRECT_ALL);
            match direct {
                [] => {}
                [edge] => {
                    let edge = &ir[*edge];
                    if edge.edge_type == EdgeType::Regular {
                        let target = edge.destination;
                        if target == head {
                            return None;
                        }
                        if Some(target) != post && !destinations.contains(&target) {
                            if post.is_some() {
                                return None;
                            }
                            let predecessors: IndexSet<_> = target
                                .get_neighbours(ir, regular, Backward)
                                .into_iter()
                                .collect();
                            if predecessors.len() <= 1 {
                                return None;
                            }
                            post = Some(target);
                            continue 'retry;
                        }
                    }
                }
                _ => {
                    if direct
                        .iter()
                        .any(|&edge| destinations.contains(&ir[edge].destination))
                    {
                        return None;
                    }
                    if post.replace(stat).is_some() {
                        return None;
                    }
                    continue 'retry;
                }
            }

            statements.push(stat);
        }

        statements.push(head);
        return Some((post, statements));
    }
}

fn choice_predecessors(ir: &Ir, stat: StatId, head: StatId) -> IndexSet<StatId> {
    stat.get_neighbours(ir, EdgeType::Regular.mask(), Backward)
        .into_iter()
        .filter(|&pred| pred != head)
        .collect()
}

pub(super) fn get_unique_pred_exceptions(ir: &Ir, head: StatId) -> IndexSet<StatId> {
    head.get_neighbours(ir, EdgeType::Exception.mask(), Forward)
        .into_iter()
        .filter(|&handler| {
            ir[handler]
                .edge_view(Backward, EdgeType::Exception.mask())
                .len()
                <= 1
        })
        .collect()
}

pub(super) fn invalid_head_merge(ir: &Ir, head: StatId, try_loop_fix: bool) -> bool {
    if try_loop_fix {
        let mut current = head;
        loop {
            match ir[current].kind {
                StatementKind::If(_) => {
                    return ir[head].continue_set.contains(&ir[current].first.unwrap());
                }
                StatementKind::Sequence => current = ir[current].first.unwrap(),
                _ => break,
            }
        }
    }
    false
}
