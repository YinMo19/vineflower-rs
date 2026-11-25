// Copyright 2000-2024 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Sparse variable version analysis on a method's direct graph.

mod dataflow;
mod maps;
mod process_expr;
mod reassign;
mod ssa;
mod ssau;

use rustc_hash::FxHashMap;

use crate::decompiler::exps::{ExprKind, STACK_BASE};
use crate::decompiler::flow::DirectGraph;
use crate::decompiler::ir::{ExprId, Ir, StatId};
use crate::decompiler::vars::var_version_pair::VarVersionPair as Version;
use crate::structs::StructMethod;

use maps::VarMapHolder;
pub use maps::{VersionMap, Versions};
pub use reassign::{InstructionRewrites, reassign_ssa, reset_versions};
pub use ssa::Ssa;
pub use ssau::Ssau;
pub(crate) use ssau::first_protected_range;

pub struct VariableVersions<A> {
    pub graph: DirectGraph,
    pub versions: A,
    /// Reads counted at every visit during the fixed-point iteration.
    pub read_counts: FxHashMap<Version, i32>,
}

pub type SsaResult = VariableVersions<Ssa>;

pub fn split_ssa(ir: &mut Ir, root: StatId, method: &StructMethod) -> SsaResult {
    dataflow::split(ir, root, method, Ssa::default())
}

pub type SsauResult = VariableVersions<Ssau>;

pub fn split_ssau(ir: &mut Ir, root: StatId, method: &StructMethod) -> SsauResult {
    let mut result = dataflow::split(ir, root, method, Ssau::default());
    result.versions.graph.init_dominators();
    result
}

/// The direct-graph propagation is common to SSA and SSAU. The two analyses
/// assign different versions to the same read and retain different dependencies.
trait VersionAnalysis {
    const CALCULATE_LIVENESS: bool = false;
    const TRACK_FIELDS: bool = false;
    const TRACK_DIRECT_ASSIGNMENTS: bool = false;

    fn init_parameter(&mut self, var: i32, catch: bool) -> i32;
    fn init_write(&mut self, ir: &Ir, stat: StatId, pair: Version) -> i32;
    fn read_single(
        &mut self,
        ir: &Ir,
        stat: StatId,
        pair: Version,
        last: i32,
        map: &mut VersionMap,
        live: bool,
    ) -> i32;
    fn read_multiple(
        &mut self,
        ir: &Ir,
        stat: StatId,
        pair: Version,
        reaching: Versions,
        map: &mut VersionMap,
        live: bool,
    ) -> i32;
    fn on_assignment(&mut self, _pair: Version, _map: &VersionMap, _live: bool) {}
    fn mark_assignment(&mut self, _left: Version, _right: Version) {}
    fn phantom(&mut self, var: Version) -> Version {
        var
    }
    fn field_index(&mut self, _expr_id: i32) -> i32 {
        -1
    }
}

#[derive(Default)]
struct VersionCounters(FxHashMap<i32, i32>);

impl VersionCounters {
    fn next(&mut self, var: i32) -> i32 {
        let version = self.0.entry(var).or_default();
        *version += 1;
        *version
    }
}

struct Transfer<'a, A> {
    analysis: &'a mut A,
    stat: StatId,
    live: bool,
    catchable: Option<&'a mut VersionMap>,
    reads: &'a mut FxHashMap<Version, i32>,
}

fn variable(ir: &Ir, expr: ExprId) -> Version {
    let ExprKind::Variable(var) = &ir[expr].kind else {
        unreachable!("expected a variable")
    };
    Version::new(var.index, var.version)
}

fn set_version(ir: &mut Ir, expr: ExprId, version: i32) {
    let ExprKind::Variable(var) = &mut ir[expr].kind else {
        unreachable!("expected a variable")
    };
    var.version = version;
}

impl<A: VersionAnalysis> Transfer<'_, A> {
    fn var_read(&mut self, ir: &mut Ir, expr: ExprId, maps: &mut VarMapHolder) {
        let pair = variable(ir, expr);
        let map = maps.normal_mut();
        let versions = map.get(pair.var);
        match versions.map_or(0, Versions::cardinality) {
            0 => self.assign(ir, expr, map),
            1 => {
                let last = versions.unwrap().iter().next().unwrap();
                let version = self
                    .analysis
                    .read_single(ir, self.stat, pair, last, map, self.live);
                set_version(ir, expr, version);
            }
            _ => {
                let reaching = versions.unwrap().clone();
                let version = self
                    .analysis
                    .read_multiple(ir, self.stat, pair, reaching, map, self.live);
                set_version(ir, expr, version);
            }
        }
        *self.reads.entry(variable(ir, expr)).or_default() += 1;
    }

    fn assign(&mut self, ir: &mut Ir, expr: ExprId, map: &mut VersionMap) {
        let mut pair = variable(ir, expr);
        pair.version = self.analysis.init_write(ir, self.stat, pair);
        set_version(ir, expr, pair.version);
        self.analysis.on_assignment(pair, map, self.live);
        map.set_current(pair.var, pair.version);
        if (0..STACK_BASE).contains(&pair.var)
            && let Some(catchable) = &mut self.catchable
            && let Some(set) = catchable.get_mut(pair.var)
        {
            set.add(pair.version);
        }
        // For a previously absent catchable slot, Java writes the singleton
        // to the normal map a second time. Its contents are already set above.
    }

    fn field_read(&mut self, ir: &Ir, expr: ExprId, map: &mut VersionMap) {
        if A::TRACK_FIELDS {
            map.set_current(self.analysis.field_index(ir[expr].id), 1);
        }
    }
}
