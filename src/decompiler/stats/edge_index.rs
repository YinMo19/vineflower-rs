use itertools::Either;
use rustc_hash::FxHashMap;

use super::stat_edge::EdgeType;
use super::{STATEDGE_ALL, STATEDGE_DIRECT_ALL};
use crate::decompiler::ir::EdgeId;

/// The same edge can appear in typed, direct and all-edge views. With one
/// entry those views only need a membership mask. Once a view contains two
/// entries its order is independent, including when an edge changes type.
#[derive(Default)]
pub(super) enum EdgeIndex {
    #[default]
    Empty,
    One {
        views: u32,
        edge: EdgeId,
    },
    Lists(Box<FxHashMap<u32, Vec<EdgeId>>>),
}

impl EdgeIndex {
    pub(super) fn view(&self, mask: u32) -> &[EdgeId] {
        match self {
            Self::One { views, edge } if views & mask != 0 => std::slice::from_ref(edge),
            Self::Lists(lists) => lists.get(&mask).map_or(&[], Vec::as_slice),
            _ => &[],
        }
    }

    pub(super) fn edges(&self) -> impl Iterator<Item = EdgeId> + '_ {
        match self {
            Self::Empty => Either::Left(None.into_iter()),
            Self::One { edge, .. } => Either::Left(Some(*edge).into_iter()),
            Self::Lists(lists) => Either::Right(lists.values().flatten().copied()),
        }
    }

    pub(super) fn add(&mut self, mask: u32, edge: EdgeId) {
        match self {
            Self::Empty => *self = Self::One { views: mask, edge },
            Self::One {
                views,
                edge: stored,
            } if *stored == edge && *views & mask == 0 => {
                *views |= mask;
            }
            Self::One {
                views,
                edge: stored,
            } => {
                let mut lists = FxHashMap::default();
                for view in EdgeType::TYPES
                    .into_iter()
                    .map(EdgeType::mask)
                    .chain([STATEDGE_ALL, STATEDGE_DIRECT_ALL])
                    .filter(|view| *views & view != 0)
                {
                    lists.insert(view, vec![*stored]);
                }
                lists.entry(mask).or_default().push(edge);
                *self = Self::Lists(Box::new(lists));
            }
            Self::Lists(lists) => lists.entry(mask).or_default().push(edge),
        }
    }

    pub(super) fn remove(&mut self, mask: u32, edge: EdgeId) {
        match self {
            Self::One {
                views,
                edge: stored,
            } if *stored == edge => {
                *views &= !mask;
                if *views == 0 {
                    *self = Self::Empty;
                }
            }
            Self::Lists(lists) => {
                if let Some(edges) = lists.get_mut(&mask)
                    && let Some(index) = edges.iter().position(|entry| *entry == edge)
                {
                    edges.remove(index);
                }
            }
            _ => {}
        }
    }

    /// Statement.clearTempInformation drops the exception view and makes
    /// the all-edge view a copy of the direct view at this point in time.
    pub(super) fn clear_exceptions(&mut self) {
        match self {
            Self::Empty => {}
            Self::One { views, .. } => {
                *views &= !(EdgeType::Exception.mask() | STATEDGE_ALL);
                if *views & STATEDGE_DIRECT_ALL != 0 {
                    *views |= STATEDGE_ALL;
                }
                if *views == 0 {
                    *self = Self::Empty;
                }
            }
            Self::Lists(lists) => {
                lists.remove(&EdgeType::Exception.mask());
                if let Some(direct) = lists.get(&STATEDGE_DIRECT_ALL).cloned() {
                    lists.insert(STATEDGE_ALL, direct);
                } else {
                    lists.remove(&STATEDGE_ALL);
                }
            }
        }
    }
}
