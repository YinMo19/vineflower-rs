//! `modules.decompiler.StatEdge`: a typed edge in the statement graph.

use arcstr::ArcStr;

use super::EdgeDirection::{Backward, Forward};
use super::{STATEDGE_ALL, STATEDGE_DIRECT_ALL};
use crate::decompiler::ir::{EdgeId, Ir, StatId};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum EdgeType {
    Regular = 1,
    Exception = 2,
    Break = 4,
    Continue = 8,
    FinallyExit = 32,
}

impl EdgeType {
    pub const TYPES: [Self; 5] = [
        Self::Regular,
        Self::Exception,
        Self::Break,
        Self::Continue,
        Self::FinallyExit,
    ];

    pub const fn mask(self) -> u32 {
        self as u32
    }

    /// Every edge appears in its typed and all-edge views. The direct view
    /// also includes it unless control is transferring to an exception handler.
    pub(super) fn index_views(self) -> impl Iterator<Item = u32> {
        [self.mask(), STATEDGE_ALL]
            .into_iter()
            .chain((self != Self::Exception).then_some(STATEDGE_DIRECT_ALL))
    }
}

#[derive(Debug)]
pub struct StatEdge {
    pub edge_type: EdgeType,
    pub source: StatId,
    pub destination: StatId,
    pub exceptions: Option<Vec<ArcStr>>,
    pub closure: Option<StatId>,
    pub labeled: bool,
    pub explicit: bool,
    pub can_inline: bool,
    pub phantom_continue: bool,
}

impl StatEdge {
    /// Allocates an edge. The source registers it using `add_successor`.
    #[expect(clippy::new_ret_no_self, reason = "edges are allocated in the IR arena")]
    pub fn new(
        ir: &mut Ir,
        edge_type: EdgeType,
        source: StatId,
        destination: StatId,
        closure: Option<StatId>,
    ) -> EdgeId {
        ir.edges.push(Self {
            edge_type,
            source,
            destination,
            exceptions: None,
            closure,
            labeled: true,
            explicit: true,
            can_inline: true,
            phantom_continue: false,
        })
    }

    pub fn new_exception(
        ir: &mut Ir,
        source: StatId,
        destination: StatId,
        exceptions: Option<Vec<ArcStr>>,
    ) -> EdgeId {
        let edge = Self::new(ir, EdgeType::Exception, source, destination, None);
        ir[edge].exceptions = exceptions;
        edge
    }
}

impl EdgeId {
    pub fn change_source(self, ir: &mut Ir, source: StatId) {
        ir[self].source.remove_edge_internal(ir, Forward, self);
        source.add_edge_internal(ir, Forward, self);
        ir[self].source = source;
    }

    pub fn change_destination(self, ir: &mut Ir, destination: StatId) {
        ir[self].destination.remove_predecessor(ir, self);
        destination.add_predecessor(ir, self);
        ir[self].destination = destination;
    }

    pub fn change_type(self, ir: &mut Ir, new_type: EdgeType) {
        let old_type = ir[self].edge_type;
        if old_type == new_type {
            return;
        }
        assert!(
            old_type != EdgeType::Exception && new_type != EdgeType::Exception,
            "Invalid edge type"
        );

        // Retyping changes the order among edges of this type. The all-edge
        // and direct-edge lists keep their existing order.
        for (stat, direction) in [(ir[self].source, Forward), (ir[self].destination, Backward)] {
            let index = ir[stat].edge_index_mut(direction);
            index.remove(old_type.mask(), self);
            index.add(new_type.mask(), self);
        }
        ir[self].edge_type = new_type;
    }

    pub fn remove(self, ir: &mut Ir) {
        ir[self].source.remove_successor(ir, self);
    }

    pub fn remove_closure(self, ir: &mut Ir) {
        assert!(ir[self].closure.is_some(), "Edge has no closure");
        self.change_closure(ir, None);
        ir[self].labeled = false;
    }

    pub fn change_closure(self, ir: &mut Ir, closure: Option<StatId>) {
        if let Some(old_closure) = ir[self].closure {
            ir[old_closure].label_edges.shift_remove(&self);
        }
        ir[self].closure = closure;
        if let Some(closure) = closure {
            ir[closure].label_edges.insert(self);
        }
    }
}
