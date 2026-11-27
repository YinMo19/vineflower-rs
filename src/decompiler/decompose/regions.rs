//! Candidate ordering and protected subgraphs from DomHelper.findGeneralStatement.
use std::collections::VecDeque;

use indexmap::{IndexMap, IndexSet};
use rustc_hash::FxHashSet;

use super::extended_postdominance::extended_postdominators;
use super::statement_order::{calc_post_dominators, post_reverse_post_order};
use crate::decompiler::ir::{Ir, StatId};
use crate::decompiler::stats::stat_edge::EdgeType;
use crate::decompiler::stats::{
    EdgeDirection::{Backward, Forward},
    STATEDGE_ALL, STATEDGE_DIRECT_ALL, Statement,
};
use crate::engine::method_timeout::checkpoint;
use crate::engine::counter_container::CounterContainer;
use crate::util::{jhash::JHashMap, vb_style_collection::VBStyleCollection};

/// parseGraph supplies a LinkedHashMap. Retries and independent subregions
/// allocate a HashMap. Its key order affects how old post sets are merged.
pub(super) enum ExtendedPosts {
    Linked(IndexMap<i32, IndexSet<i32>>),
    Hashed(JHashMap<i32, IndexSet<i32>>),
}

impl ExtendedPosts {
    pub fn fresh() -> Self {
        Self::Hashed(JHashMap::new())
    }

    pub fn is_empty(&self) -> bool {
        match self {
            Self::Linked(m) => m.is_empty(),
            Self::Hashed(m) => m.is_empty(),
        }
    }

    fn get(&self, id: i32) -> Option<&IndexSet<i32>> {
        match self {
            Self::Linked(m) => m.get(&id),
            Self::Hashed(m) => m.get(&id),
        }
    }

    fn populate(&mut self, ir: &Ir, stat: StatId) {
        if self.is_empty() {
            let computed = extended_postdominators(ir, stat);
            match self {
                Self::Linked(m) => m.extend(computed),
                Self::Hashed(m) => {
                    let len = computed.len();
                    m.put_all(computed, len);
                }
            }
        }
    }

    pub fn collapse(&mut self, ir: &Ir, region: StatId) {
        if self.is_empty() {
            return;
        }
        let children: FxHashSet<_> = ir[region].stats.iter().map(|&s| ir[s].id).collect();
        let id = ir[region].id;
        let keys: Vec<_> = match self {
            Self::Linked(m) => m.keys().copied().collect(),
            Self::Hashed(m) => m.keys().copied().collect(),
        };
        for key in keys {
            let set = match self {
                Self::Linked(m) => m.get_mut(&key),
                Self::Hashed(m) => m.get_mut(&key),
            }
            .unwrap();
            let len = set.len();
            set.retain(|k| !children.contains(k));
            if children.contains(&key) {
                let remaining = std::mem::take(set);
                match self {
                    Self::Linked(m) => {
                        m.entry(id).or_default().extend(remaining);
                        m.shift_remove(&key);
                    }
                    Self::Hashed(m) => {
                        m.get_or_insert_with(id, IndexSet::new).extend(remaining);
                        m.remove(&key);
                    }
                }
            } else if set.len() < len {
                set.insert(id);
            }
        }
    }
}

fn all_candidates(ir: &Ir, stat: StatId, ext: &ExtendedPosts) -> VBStyleCollection<Vec<i32>, i32> {
    let mut candidates = VBStyleCollection::new();
    let stats = &ir[stat].stats;
    for source in post_reverse_post_order(ir, stat) {
        let Some(posts) = ext.get(ir[source].id) else {
            continue;
        };
        let valid: Vec<_> = posts
            .iter()
            .copied()
            .filter(|id| {
                let Some(&target) = stats.get_with_key(id) else {
                    return true;
                };
                let exits = target.get_successor_edges(ir, EdgeType::FinallyExit.mask());
                if exits.is_empty() {
                    return true;
                }
                assert_eq!(exits.len(), 1, "Expected one exit from a finally end block");
                target
                    .get_predecessor_edges(ir, STATEDGE_ALL)
                    .iter()
                    .any(|&edge| ir[edge].source == source)
            })
            .collect();
        candidates.add_with_key(valid, ir[source].id);
    }
    if let Some(tails) = ext.get(ir[ir[stat].first.unwrap()].id) {
        for &id in tails {
            if let Some(posts) = candidates.get_with_key_mut(&id) {
                posts.push(id);
            } else {
                candidates.add_with_key(vec![id], id);
            }
        }
    }
    candidates
}

pub(super) fn find_general(
    ir: &mut Ir,
    counters: &mut CounterContainer,
    stat: StatId,
    force_all: bool,
    ext: &mut ExtendedPosts,
) -> Option<StatId> {
    ext.populate(ir, stat);
    let candidates = if force_all {
        all_candidates(ir, stat, ext)
    } else {
        calc_post_dominators(ir, stat)
    };
    for (index, posts) in candidates.iter().enumerate() {
        checkpoint();
        let head_id = *candidates.get_key(index).unwrap();
        let ext_set = ext.get(head_id);
        if ext_set.is_none() && posts.as_slice() != [head_id] {
            continue;
        }
        for &id in posts {
            if id != head_id && !ext_set.is_some_and(|posts| posts.contains(&id)) {
                continue;
            }
            let Some(&post) = ir[stat].stats.get_with_key(&id) else {
                continue;
            };
            // Inherited tail IDs may already have been folded in the parent.
            // Their singleton post is discarded above before Java uses the head.
            let head = *ir[stat]
                .stats
                .get_with_key(&head_id)
                .expect("missing region head");
            let Some(nodes) = region_nodes(ir, head, post, ir[stat].stats.len()) else {
                continue;
            };
            let result =
                Statement::new_general(ir, counters, head, nodes, (head != post).then_some(post));
            stat.collapse_nodes_to_statement(ir, counters, result);
            return Some(result);
        }
    }
    None
}

fn region_nodes(
    ir: &Ir,
    head: StatId,
    post: StatId,
    general_size: usize,
) -> Option<IndexSet<StatId>> {
    let normal = EdgeType::Regular.mask();
    let exception = EdgeType::Exception.mask();
    let mut nodes = IndexSet::new();
    let mut preds = FxHashSet::default();
    let mut handlers = IndexSet::from([head]);
    while let Some(handler) = handlers.iter().copied().find(|handler| {
        if nodes.contains(handler) {
            return false;
        }
        if nodes.is_empty() {
            return true;
        }
        let protected = handler.get_neighbours(ir, exception, Backward);
        (nodes.len() > protected.len() || nodes.len() == 1)
            && protected.iter().all(|stat| nodes.contains(stat))
    }) {
        let mut queue = VecDeque::from([handler]);
        while let Some(node) = queue.pop_front() {
            checkpoint();
            if (head != post && node == post) || !nodes.insert(node) {
                continue;
            }
            if node != head {
                preds.extend(node.get_neighbours(ir, normal, Backward));
            }
            queue.extend(node.get_neighbours(ir, normal, Forward));
            handlers.extend(node.get_neighbours(ir, exception, Forward));
        }
        handlers.shift_remove(&handler);
    }

    if nodes.len() >= general_size
        || !preds.iter().all(|pred| nodes.contains(pred))
        || (nodes.len() <= 1 && !head.get_neighbours(ir, normal, Backward).contains(&head))
    {
        return None;
    }
    let external_handlers: FxHashSet<_> = nodes
        .iter()
        .flat_map(|node| node.get_neighbours(ir, exception, Forward))
        .filter(|h| !nodes.contains(h))
        .collect();
    for handler in external_handlers {
        let protected: FxHashSet<_> = handler
            .get_neighbours(ir, exception, Backward)
            .into_iter()
            .collect();
        if !nodes.iter().all(|s| protected.contains(s)) {
            return None;
        }
    }
    let complete=nodes.iter().filter(|&&node| ir[node].is_monitor_enter).all(|node| {
        let edges=node.get_successor_edges(ir,STATEDGE_DIRECT_ALL);
        matches!(edges.as_slice(),[edge] if ir[*edge].edge_type==EdgeType::Regular && nodes.contains(&ir[*edge].destination))
    });
    complete.then_some(nodes)
}
