//! Statement graph traversals, strong connectivity, and postdominance.

use std::rc::Rc;

use bit_set::BitSet;
use rustc_hash::{FxHashMap, FxHashSet};

use crate::decompiler::ir::{Ir, StatId};
use crate::decompiler::stats::stat_edge::EdgeType;
use crate::decompiler::stats::{EdgeDirection, STATEDGE_ALL, STATEDGE_DIRECT_ALL};
use crate::util::vb_style_collection::VBStyleCollection;

const REGULAR: u32 = EdgeType::Regular.mask();

/// `Statement.getReversePostOrderList()`.
pub fn reverse_post_order(ir: &Ir, general: StatId) -> Vec<StatId> {
    reverse_post_order_from(ir, ir[general].first.expect("Statement has no first child"))
}

/// `Statement.getReversePostOrderList(start)`.
pub fn reverse_post_order_from(ir: &Ir, start: StatId) -> Vec<StatId> {
    depth_first_order([start], |node| {
        // Regular and exception edges are interleaved in the all-edge list.
        node.get_successor_edges(ir, STATEDGE_ALL)
            .into_iter()
            .filter_map(|edge| {
                let edge = &ir[edge];
                matches!(edge.edge_type, EdgeType::Regular | EdgeType::Exception)
                    .then_some(edge.destination)
            })
            .collect()
    })
}

/// `Statement.getPostReversePostOrderList()`.
pub fn post_reverse_post_order(ir: &Ir, general: StatId) -> Vec<StatId> {
    let exits = exit_reps(ir, &components(ir, general));
    post_reverse_post_order_from(ir, general, &exits)
}

/// `Statement.getPostReversePostOrderList(exits)`.
pub fn post_reverse_post_order_from(ir: &Ir, general: StatId, exits: &[StatId]) -> Vec<StatId> {
    let order = depth_first_order(exits.iter().copied(), |node| {
        // A combined mask walks the regular predecessors before the exception predecessors.
        node.get_neighbours(
            ir,
            REGULAR | EdgeType::Exception.mask(),
            EdgeDirection::Backward,
        )
    });
    assert_eq!(
        order.len(),
        ir[general].stats.len(),
        "computing post reverse post order failed!"
    );
    order
}

fn depth_first_order(
    roots: impl IntoIterator<Item = StatId>,
    neighbours: impl Fn(StatId) -> Vec<StatId>,
) -> Vec<StatId> {
    let mut visited = FxHashSet::default();
    let mut order = Vec::new();
    let mut stack = Vec::new();
    for root in roots {
        if !visited.insert(root) {
            continue;
        }
        stack.push((root, neighbours(root).into_iter()));
        while let Some((node, next)) = stack.last_mut() {
            if let Some(successor) = next.next() {
                if visited.insert(successor) {
                    stack.push((successor, neighbours(successor).into_iter()));
                }
            } else {
                order.push(*node);
                stack.pop();
            }
        }
    }
    // Upstream prepends each finished node to the same list across all roots.
    order.reverse();
    order
}

/// `StrongConnectivityHelper.getComponents()`, in discovery and stack-pop order.
pub fn components(ir: &Ir, general: StatId) -> Vec<Vec<StatId>> {
    let mut search = ComponentSearch::default();
    search.visit_tree(ir, ir[general].first.expect("Statement has no first child"));

    for &stat in &ir[general].stats {
        if !search.processed.contains(&stat)
            && stat
                .get_predecessor_edges(ir, STATEDGE_DIRECT_ALL)
                .is_empty()
        {
            search.visit_tree(ir, stat);
        }
    }
    for &stat in &ir[general].stats {
        if !search.processed.contains(&stat) {
            search.visit_tree(ir, stat);
        }
    }
    search.components
}

struct Visit {
    index: usize,
    low_link: usize,
    visited: bool,
    on_stack: bool,
}

#[derive(Default)]
struct ComponentSearch {
    components: Vec<Vec<StatId>>,
    processed: FxHashSet<StatId>,
    stack: Vec<StatId>,
    visits: FxHashMap<StatId, Visit>,
    next_index: usize,
}

impl ComponentSearch {
    fn start_visit(&mut self, ir: &Ir, stat: StatId, visited: bool) -> std::vec::IntoIter<StatId> {
        self.stack.push(stat);
        self.visits.insert(
            stat,
            Visit {
                index: self.next_index,
                low_link: self.next_index,
                visited,
                on_stack: true,
            },
        );
        self.next_index += 1;
        stat.get_neighbours(ir, REGULAR, EdgeDirection::Forward)
            .into_iter()
    }

    fn visit_tree(&mut self, ir: &Ir, root: StatId) {
        self.stack.clear();
        self.next_index = 0;

        // Upstream marks a node visited upon following an edge to it. A back
        // edge to the tree root can therefore enter it again.
        let mut frames = vec![(root, self.start_visit(ir, root, false))];
        while let Some((stat, successors)) = frames.last_mut() {
            let stat = *stat;
            if let Some(successor) = successors.next() {
                if self.processed.contains(&successor) {
                    continue;
                }
                match self.visits.get(&successor) {
                    Some(visit) if visit.visited => {
                        if visit.on_stack {
                            self.lower_link(stat, visit.index);
                        }
                    }
                    _ => frames.push((successor, self.start_visit(ir, successor, true))),
                }
                continue;
            }

            let visit = &self.visits[&stat];
            if visit.low_link == visit.index {
                let mut component = Vec::new();
                loop {
                    let member = self.stack.pop().expect("Missing component root");
                    self.visits.get_mut(&member).unwrap().on_stack = false;
                    component.push(member);
                    if member == stat {
                        break;
                    }
                }
                self.components.push(component);
            }
            frames.pop();
            if let Some(&(parent, _)) = frames.last() {
                self.lower_link(parent, self.visits[&stat].low_link);
            }
        }
        self.processed
            .extend(std::mem::take(&mut self.visits).into_keys());
    }

    fn lower_link(&mut self, stat: StatId, other_index: usize) {
        let visit = self.visits.get_mut(&stat).unwrap();
        visit.low_link = visit.low_link.min(other_index);
    }
}

/// `StrongConnectivityHelper.isExitComponent`.
pub fn is_exit_component(ir: &Ir, component: &[StatId]) -> bool {
    let members: FxHashSet<_> = component.iter().copied().collect();
    component.iter().all(|&stat| {
        stat.get_neighbours(ir, REGULAR, EdgeDirection::Forward)
            .iter()
            .all(|succ| members.contains(succ))
    })
}

/// The first member of each component with no outgoing regular edge.
pub fn exit_reps(ir: &Ir, components: &[Vec<StatId>]) -> Vec<StatId> {
    components
        .iter()
        .filter(|component| is_exit_component(ir, component))
        .map(|component| component[0])
        .collect()
}

/// `DomHelper.calcPostDominators`.
pub fn calc_post_dominators(ir: &Ir, general: StatId) -> VBStyleCollection<Vec<i32>, i32> {
    let components = components(ir, general);
    let exits = exit_reps(ir, &components);
    let order = post_reverse_post_order_from(ir, general, &exits);
    let positions: FxHashMap<_, _> = order
        .iter()
        .enumerate()
        .map(|(index, &stat)| (stat, index))
        .collect();

    let mut pending = BitSet::<u64>::with_capacity_general(order.len());
    pending.get_mut().fill(true);
    let all = Rc::new(pending.clone());
    let mut dominators = vec![Rc::clone(&all); order.len()];
    for component in components {
        let initial = if is_exit_component(ir, &component) {
            let mut set = BitSet::<u64>::with_capacity_general(order.len());
            set.extend(component.iter().map(|stat| positions[stat]));
            Rc::new(set)
        } else {
            Rc::clone(&all)
        };
        for stat in component {
            dominators[positions[&stat]] = Rc::clone(&initial);
        }
    }

    let mut next = BitSet::<u64>::with_capacity_general(order.len());
    while !pending.is_empty() {
        for (index, &stat) in order.iter().enumerate() {
            if !pending.remove(index) {
                continue;
            }

            let mut successors = stat
                .get_neighbours(ir, REGULAR, EdgeDirection::Forward)
                .into_iter();
            if let Some(first) = successors.next() {
                next.clone_from(&dominators[positions[&first]]);
                for succ in successors {
                    next.intersect_with(&dominators[positions[&succ]]);
                }
            } else {
                next.make_empty();
            }
            next.insert(index);

            if next.get_ref() != dominators[index].get_ref() {
                dominators[index] = Rc::new(next.clone());
                for pred in stat.get_neighbours(ir, REGULAR, EdgeDirection::Backward) {
                    pending.insert(positions[&pred]);
                }
            }
        }
    }

    let sort_order: FxHashMap<_, _> = reverse_post_order(ir, general)
        .into_iter()
        .enumerate()
        .map(|(index, stat)| (ir[stat].id, index))
        .collect();
    let mut result = VBStyleCollection::with_capacity(order.len());
    for (stat, set) in order.iter().zip(dominators) {
        let id = ir[*stat].id;
        let mut posts: Vec<_> = set.iter().map(|index| ir[order[index]].id).collect();
        posts.sort_by_key(|post| sort_order[post]);
        if posts.len() > 1 && posts[0] == id {
            posts.rotate_left(1);
        }
        result.add_with_key(posts, id);
    }
    result
}
