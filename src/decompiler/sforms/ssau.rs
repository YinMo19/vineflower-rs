//! Sparse SSA with a distinct version for each use.

use rustc_hash::{FxHashMap, FxHashSet};

use super::{Version, VersionAnalysis, VersionCounters, VersionMap, Versions};
use crate::decompiler::ir::{Ir, StatId};
use crate::decompiler::stats::StatementKind;
use crate::decompiler::vars::version_graph::{VarVersionsGraph, VersionState};

pub struct Ssau {
    pub graph: VarVersionsGraph,
    pub assignments: FxHashMap<Version, Version>,
    pub first_range: FxHashMap<Version, i32>,
    pub field_vars: FxHashMap<i32, i32>,
    counters: VersionCounters,
    next_field: i32,
    missing_version: Option<Version>,
}

impl Default for Ssau {
    fn default() -> Self {
        Self {
            graph: VarVersionsGraph::default(),
            assignments: FxHashMap::default(),
            first_range: FxHashMap::default(),
            field_vars: FxHashMap::default(),
            counters: VersionCounters::default(),
            next_field: -1,
            missing_version: None,
        }
    }
}

impl VersionAnalysis for Ssau {
    const TRACK_FIELDS: bool = true;
    const TRACK_DIRECT_ASSIGNMENTS: bool = true;
    const CALCULATE_LIVENESS: bool = true;

    fn missing_version(&self) -> Option<Version> {
        self.missing_version
    }

    fn init_parameter(&mut self, var: i32, catch: bool) -> i32 {
        let state = if catch {
            VersionState::Catch
        } else {
            VersionState::Param
        };
        self.create_version(var, None, state).version
    }

    fn init_write(&mut self, ir: &Ir, stat: StatId, pair: Version) -> i32 {
        if pair.version != 0 {
            pair.version
        } else {
            let range = first_protected_range(ir, stat).map(|stat| ir[stat].id);
            self.create_version(pair.var, range, VersionState::Write)
                .version
        }
    }

    fn read_single(
        &mut self,
        ir: &Ir,
        stat: StatId,
        pair: Version,
        last: i32,
        map: &mut VersionMap,
        live: bool,
    ) -> i32 {
        let version = if pair.version == 0 {
            let range = first_protected_range(ir, stat).map(|stat| ir[stat].id);
            self.create_read(Version::new(pair.var, last), range)
                .map_or(last, |pair| pair.version)
        } else {
            pair.version
        };
        self.update_live(pair, map, live);
        map.set_current(pair.var, version);
        version
    }

    fn read_multiple(
        &mut self,
        ir: &Ir,
        stat: StatId,
        mut pair: Version,
        reaching: Versions,
        map: &mut VersionMap,
        live: bool,
    ) -> i32 {
        let range = first_protected_range(ir, stat).map(|stat| ir[stat].id);
        if pair.version == 0 {
            pair = self.create_version(pair.var, range, VersionState::Phi);
        }
        self.update_live(pair, map, live);
        map.set_current(pair.var, pair.version);
        self.update_phi(pair, &reaching, range);
        pair.version
    }

    fn on_assignment(&mut self, pair: Version, map: &VersionMap, live: bool) {
        self.update_live(pair, map, live);
    }

    fn mark_assignment(&mut self, left: Version, right: Version) {
        self.assignments.insert(left, right);
    }

    fn phantom(&mut self, pair: Version) -> Version {
        let Some(node) = self.graph.get(pair) else {
            self.missing_version.get_or_insert(pair);
            return pair;
        };
        if let Some(phantom) = node.phantom_node {
            return phantom;
        }
        let phantom = self.create_version(pair.var, None, VersionState::Phantom);
        self.graph[pair].phantom_node = Some(phantom);
        self.graph[phantom].phantom_parent_node = Some(pair);
        phantom
    }

    fn field_index(&mut self, expr_id: i32) -> i32 {
        *self.field_vars.entry(expr_id).or_insert_with(|| {
            let field = self.next_field;
            self.next_field -= 1;
            self.graph.create_node(Version::new(field, 1), None, None);
            field
        })
    }
}

impl Ssau {
    fn create_version(&mut self, var: i32, range: Option<i32>, state: VersionState) -> Version {
        let pair = Version::new(var, self.counters.next(var));
        self.graph.create_node(pair, None, Some(state));
        if let Some(range) = range {
            self.first_range.insert(pair, range);
        }
        pair
    }

    fn create_read(&mut self, source: Version, range: Option<i32>) -> Option<Version> {
        if self.graph.get(source).is_none() {
            self.missing_version.get_or_insert(source);
            return None;
        }
        let read = self.create_version(source.var, range, VersionState::Read);
        self.graph.add_read_edge(source, read);
        Some(read)
    }

    fn update_live(&mut self, pair: Version, map: &VersionMap, live: bool) {
        if live {
            if let Some(node) = self.graph.nodes.get_with_key_mut(&pair) {
                node.live = Some(map.clone());
            } else {
                self.missing_version.get_or_insert(pair);
            }
        }
    }

    fn update_phi(&mut self, phi: Version, reaching: &Versions, range: Option<i32>) {
        let Some(node) = self.graph.get(phi) else {
            self.missing_version.get_or_insert(phi);
            return;
        };
        let mut existing = FxHashSet::default();
        let predecessors = &node.predecessors;
        match predecessors.len() {
            0 => {}
            1 => {
                // A read with one source acquired another source during
                // fixed-point iteration. It now needs a phi.
                let source = self.graph[phi].single_predecessor();
                self.graph[phi].state = Some(VersionState::Phi);
                self.graph.remove_read_edge(source, phi);
            }
            _ => {
                let mut dead = Vec::new();
                for &read in predecessors {
                    let source = self.graph[read].single_predecessor().version;
                    if reaching.contains(&source) {
                        existing.insert(source);
                    } else {
                        dead.push(read);
                    }
                }
                for read in dead {
                    self.graph.remove_read_edge(read, phi);
                    self.graph[read].state = Some(VersionState::DeadRead);
                }
            }
        }
        for version in reaching {
            if !existing.contains(&version) {
                let Some(read) = self.create_read(Version::new(phi.var, version), range) else {
                    return;
                };
                self.graph.add_read_edge(read, phi);
            }
        }
    }
}

/// The closest enclosing try range for this statement. Handlers belong to an
/// enclosing try range only if one of its ancestors enters the protected body.
pub fn first_protected_range(ir: &Ir, mut stat: StatId) -> Option<StatId> {
    while let Some(parent) = ir[stat].parent {
        let protects = match ir[parent].kind {
            StatementKind::Catch { .. } | StatementKind::CatchAll { .. } => {
                ir[parent].first == Some(stat)
            }
            StatementKind::Synchronized { body, .. } => body == stat,
            _ => false,
        };
        if protects {
            return Some(parent);
        }
        stat = parent;
    }
    None
}
