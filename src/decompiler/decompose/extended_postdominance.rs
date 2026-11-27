//! Extended postdominators used to split a partially decomposed general
//! statement into smaller subgraphs.

use std::collections::VecDeque;

use bit_set::BitSet;
use indexmap::{IndexMap, IndexSet};
use rustc_hash::{FxHashMap, FxHashSet};

use super::generic_dominator_engine::GenericDominatorEngine;
use super::statement_order::{components, reverse_post_order};
use crate::decompiler::ir::{Ir, StatId};
use crate::decompiler::stats::stat_edge::{EdgeType, StatEdge};
use crate::decompiler::stats::{EdgeDirection, STATEDGE_ALL, STATEDGE_DIRECT_ALL, StatementKind};
use crate::engine::method_timeout::checkpoint;
use crate::util::jhash::JHashMap;

const REGULAR: u32 = EdgeType::Regular.mask();
const EXCEPTION: u32 = EdgeType::Exception.mask();
const CONTINUE: u32 = EdgeType::Continue.mask();

/// Like upstream's fixed sets, the bits follow the general statement's child
/// order. The result converts each set to ascending statement ID order.
type StatementSet = BitSet<u64>;
type ExtendedSets = IndexMap<StatId, StatementSet>;
type SupportPoints = FxHashMap<StatId, StatementSet>;
type ReachabilitySets = FxHashMap<StatId, Option<StatementSet>>;

pub fn extended_postdominators(ir: &Ir, general: StatId) -> IndexMap<i32, IndexSet<i32>> {
    assert!(matches!(ir[general].kind, StatementKind::General { .. }));
    ExtendedPostdominance {
        ir,
        general,
        order: reverse_post_order(ir, general),
    }
    .calculate()
}

struct ExtendedPostdominance<'a> {
    ir: &'a Ir,
    general: StatId,
    order: Vec<StatId>,
}

impl ExtendedPostdominance<'_> {
    fn calculate(&self) -> IndexMap<i32, IndexSet<i32>> {
        let ir = self.ir;
        let mut extended = self.default_reachable_sets();
        let mut support_points = self.calculate_support_points(REGULAR, true);
        self.remove_erroneous_nodes(&mut extended, &mut support_points);

        let first = ir[self.general].first.unwrap();
        let dominators = GenericDominatorEngine::new(
            &self.order,
            |stat| stat == first,
            |stat| stat.get_neighbours(ir, STATEDGE_ALL, EdgeDirection::Backward),
        );
        let filter = DominatorTreeExceptionFilter::new(ir, self.general, &self.order, &dominators);
        extended.retain(|&head, posts| {
            *posts = posts
                .iter()
                .filter(|&index| filter.accepts(head, ir[self.statement_at(index)].id))
                .collect();
            !posts.is_empty()
        });
        self.filter_on_dominance(&mut extended, &dominators);
        self.add_supported_components(&mut extended, &support_points, &dominators);

        // FastExtendedPostdominanceHelper copies the surviving LinkedHashMap
        // entries into a plain HashMap sized to the number of survivors.
        let mut result = JHashMap::with_capacity(extended.len());
        for (head, posts) in extended {
            result.insert(ir[head].id, posts);
        }
        result
            .iter()
            .map(|(&head, posts)| {
                let mut ids: Vec<_> = posts
                    .iter()
                    .map(|index| ir[self.statement_at(index)].id)
                    .collect();
                ids.sort_unstable();
                (head, ids.into_iter().collect())
            })
            .collect()
    }

    fn position(&self, stat: StatId) -> usize {
        self.ir[self.general]
            .stats
            .get_index_by_key(&self.ir[stat].id)
    }

    fn statement_at(&self, index: usize) -> StatId {
        self.ir[self.general].stats[index]
    }

    fn default_reachable_sets(&self) -> ExtendedSets {
        let edge_types = REGULAR | EXCEPTION;
        let mut support_points = self.calculate_support_points(edge_types, false);
        let mut extended: ExtendedSets = self.ir[self.general]
            .stats
            .iter()
            .map(|&stat| (stat, StatementSet::default()))
            .collect();
        self.iterate_reachability(edge_types, &mut support_points, |stat, sets, _| {
            let index = self.position(stat);
            for start in sets[&stat].as_ref().unwrap() {
                extended[&self.statement_at(start)].insert(index);
            }
            false
        });
        extended
    }

    fn remove_erroneous_nodes(
        &self,
        extended: &mut ExtendedSets,
        support_points: &mut SupportPoints,
    ) {
        let ir = self.ir;
        self.iterate_reachability(REGULAR, support_points, |stat, sets, support_points| {
            let index = self.position(stat);
            let reachable = sets[&stat].as_ref().unwrap();
            let predecessors: Vec<_> = stat
                .get_predecessor_edges(ir, REGULAR)
                .into_iter()
                .map(|edge| {
                    predecessor_reachability(ir[edge].source, sets, support_points).unwrap()
                })
                .collect();

            for start in reachable {
                let mut predecessor_sets = predecessors
                    .iter()
                    .copied()
                    .filter(|set| set.contains(start));
                let mut intersection = predecessor_sets.next().cloned().unwrap_or_default();
                for set in predecessor_sets {
                    intersection.intersect_with(set);
                }
                if index == start {
                    intersection.remove(index);
                } else {
                    intersection.insert(index);
                }

                let mut excluded = reachable.clone();
                excluded.difference_with(&intersection);
                extended[&self.statement_at(start)].difference_with(&excluded);
            }
            false
        });

        let handlers: StatementSet = ir[self.general]
            .stats
            .iter()
            .copied()
            .filter(|&stat| {
                stat.get_predecessor_edges(ir, STATEDGE_DIRECT_ALL)
                    .is_empty()
                    && !stat.get_predecessor_edges(ir, EXCEPTION).is_empty()
            })
            .map(|stat| self.position(stat))
            .collect();
        if !handlers.is_empty() {
            for posts in extended.values_mut() {
                posts.difference_with(&handlers);
            }
        }
    }

    fn calculate_support_points(
        &self,
        edge_types: u32,
        include_general_continue: bool,
    ) -> SupportPoints {
        let ir = self.ir;
        let mut support_points = SupportPoints::default();
        self.iterate_reachability(
            edge_types,
            &mut support_points,
            |stat, sets, support_points| {
                for edge in stat.get_successor_edges(ir, STATEDGE_ALL) {
                    let edge = &ir[edge];
                    if edge.edge_type.mask() & edge_types == 0
                        && !(include_general_continue && edge.edge_type == EdgeType::Continue)
                    {
                        continue;
                    }
                    if let Some(destination) = self.local_successor(edge)
                        && sets.contains_key(&destination)
                    {
                        let reachable = sets[&stat].as_ref().unwrap();
                        if support_points.get(&stat) != Some(reachable) {
                            support_points.insert(stat, reachable.clone());
                            return true;
                        }
                    }
                }
                false
            },
        );
        support_points
    }

    fn local_successor(&self, edge: &StatEdge) -> Option<StatId> {
        if edge.edge_type != EdgeType::Continue {
            Some(edge.destination)
        } else if edge.destination == self.general {
            self.ir[self.general].first
        } else {
            None
        }
    }

    fn iterate_reachability(
        &self,
        edge_types: u32,
        support_points: &mut SupportPoints,
        mut visit: impl FnMut(StatId, &ReachabilitySets, &mut SupportPoints) -> bool,
    ) {
        let ir = self.ir;
        let mut sets = ReachabilitySets::default();

        loop {
            let mut changed = false;
            sets.clear();
            for &stat in &self.order {
                checkpoint();
                let predecessors: Vec<_> = stat
                    .get_predecessor_edges(ir, STATEDGE_ALL)
                    .into_iter()
                    .filter(|&edge| ir[edge].edge_type.mask() & edge_types != 0)
                    .map(|edge| ir[edge].source)
                    .collect();
                let mut reachable = StatementSet::default();
                reachable.insert(self.position(stat));
                for &predecessor in &predecessors {
                    if let Some(set) = predecessor_reachability(predecessor, &sets, support_points)
                    {
                        reachable.union_with(set);
                    }
                }
                sets.insert(stat, Some(reachable));
                changed |= visit(stat, &sets, support_points);

                // Keep the key after disposing of its set. Later nodes still
                // need to know which predecessors and successors were visited.
                for predecessor in predecessors {
                    if sets.contains_key(&predecessor)
                        && predecessor
                            .get_successor_edges(ir, STATEDGE_ALL)
                            .into_iter()
                            .all(|edge| {
                                ir[edge].edge_type.mask() & edge_types == 0
                                    || sets.contains_key(&ir[edge].destination)
                            })
                    {
                        sets.insert(predecessor, None);
                    }
                }
            }
            if !changed {
                break;
            }
        }
    }

    fn filter_on_dominance(
        &self,
        extended: &mut ExtendedSets,
        dominators: &GenericDominatorEngine<StatId>,
    ) {
        let ir = self.ir;
        extended.retain(|&head, posts| {
            let mut queue = VecDeque::from([(head, StatementSet::default())]);
            let mut visited = FxHashSet::default();
            visited.insert(head);

            while let Some((stat, mut path)) = queue.pop_front() {
                checkpoint();
                let index = self.position(stat);
                if posts.contains(index) {
                    path.insert(index);
                }
                if posts.is_subset(&path) {
                    continue;
                }
                if !dominators.is_dominator(stat, head) {
                    posts.difference_with(&path);
                    continue;
                }
                for edge in stat.get_successor_edges(ir, REGULAR | CONTINUE) {
                    if let Some(destination) = self.local_successor(&ir[edge])
                        && visited.insert(destination)
                    {
                        queue.push_back((destination, path.clone()));
                    }
                }
            }

            !posts.is_empty()
        });
    }

    fn add_supported_components(
        &self,
        extended: &mut ExtendedSets,
        support_points: &SupportPoints,
        dominators: &GenericDominatorEngine<StatId>,
    ) {
        for component in components(self.ir, self.general) {
            if let Some(head) =
                supported_component_header(self.ir, &component, support_points, dominators)
            {
                let head_index = self.position(head);
                for stat in component.into_iter().filter(|&stat| stat != head) {
                    extended.entry(stat).or_default().insert(head_index);
                }
            }
        }
    }
}

fn predecessor_reachability<'a>(
    predecessor: StatId,
    sets: &'a ReachabilitySets,
    support_points: &'a SupportPoints,
) -> Option<&'a StatementSet> {
    sets.get(&predecessor)
        .and_then(Option::as_ref)
        .or_else(|| support_points.get(&predecessor))
}

fn supported_component_header(
    ir: &Ir,
    component: &[StatId],
    support_points: &SupportPoints,
    dominators: &GenericDominatorEngine<StatId>,
) -> Option<StatId> {
    let mut supported = None;
    for &stat in component
        .iter()
        .filter(|stat| support_points.contains_key(stat))
    {
        for successor in stat.get_neighbours(ir, REGULAR, EdgeDirection::Forward) {
            if !component.contains(&successor) {
                return None;
            }
            if dominators.is_dominator(stat, successor) {
                if supported.is_some_and(|previous| previous != successor) {
                    return None;
                }
                supported = Some(successor);
            }
        }
    }
    supported?;

    let mut entries = component.iter().copied().flat_map(|stat| {
        stat.get_neighbours(ir, REGULAR, EdgeDirection::Backward)
            .into_iter()
            .filter(|source| !component.contains(source))
            .map(move |_| stat)
    });
    let head = entries.next()?;
    if entries.next().is_some()
        || component
            .iter()
            .any(|&stat| !dominators.is_dominator(stat, head))
    {
        return None;
    }
    Some(head)
}

const MULTIPLE_RANGE_EXITS: i32 = -1;

struct DominatorTreeExceptionFilter {
    exception_dominators: FxHashMap<StatId, StatId>,
    range_exits: FxHashMap<StatId, FxHashMap<StatId, i32>>,
}

impl DominatorTreeExceptionFilter {
    fn new(
        ir: &Ir,
        general: StatId,
        order: &[StatId],
        dominators: &GenericDominatorEngine<StatId>,
    ) -> Self {
        let mut branches = vec![Vec::new(); order.len()];
        for (index, &parent) in dominators
            .immediate_dominator_positions()
            .iter()
            .enumerate()
            .rev()
        {
            if index != parent {
                branches[parent].push(index);
            }
        }

        let mut ranges = Vec::new();
        for &handler in &ir[general].stats {
            let range: FxHashSet<_> = handler
                .get_predecessor_edges(ir, EXCEPTION)
                .into_iter()
                .filter_map(|edge| {
                    let edge = &ir[edge];
                    // An exception edge into a finally handler has no type list.
                    edge.exceptions.as_ref().map(|_| edge.source)
                })
                .collect();
            if !range.is_empty() {
                ranges.push((handler, range));
            }
        }

        let mut exception_dominators: Vec<FxHashMap<StatId, StatId>> =
            vec![FxHashMap::default(); order.len()];
        let mut range_exits: FxHashMap<StatId, FxHashMap<StatId, i32>> = FxHashMap::default();

        // Immediate dominators precede their children in reverse postorder.
        // Build the same tree maps bottom-up, visiting siblings in the order
        // buildDominatorTree added them.
        for (index, &stat) in order.iter().enumerate().rev() {
            let mut doms = FxHashMap::default();
            let mut exits = FxHashMap::default();
            let protected_ranges: Vec<_> = ranges
                .iter()
                .filter(|(_, range)| range.contains(&stat))
                .collect();
            for &child in &branches[index] {
                let child_stat = order[child];
                for (handler, dominator) in std::mem::take(&mut exception_dominators[child]) {
                    doms.entry(handler)
                        .and_modify(|current| *current = stat)
                        .or_insert(dominator);
                }
                for &&(handler, ref range) in &protected_ranges {
                    let exit = if !range.contains(&child_stat) {
                        Some(ir[child_stat].id)
                    } else if exits.contains_key(&handler) {
                        Some(MULTIPLE_RANGE_EXITS)
                    } else {
                        range_exits[&child_stat].get(&handler).copied()
                    };
                    if let Some(exit) = exit {
                        exits.insert(handler, exit);
                    }
                }
            }
            for &(handler, _) in protected_ranges {
                doms.insert(handler, stat);
            }
            exception_dominators[index] = doms;
            range_exits.insert(stat, exits);
        }
        Self {
            exception_dominators: std::mem::take(&mut exception_dominators[0]),
            range_exits,
        }
    }

    fn accepts(&self, head: StatId, exit: i32) -> bool {
        self.range_exits[&head]
            .iter()
            .all(|(handler, &range_exit)| {
                self.exception_dominators.get(handler) == Some(&head)
                    || (range_exit != MULTIPLE_RANGE_EXITS && range_exit == exit)
            })
    }
}
