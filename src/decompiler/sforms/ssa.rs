//! Ordinary sparse SSA, where a read uses its reaching version or names a phi.

use super::{Version, VersionAnalysis, VersionCounters, VersionMap, Versions};
use crate::decompiler::ir::{Ir, StatId};
use crate::util::jhash::JHashMap;

#[derive(Default)]
pub struct Ssa {
    pub phi: JHashMap<Version, Versions>,
    counters: VersionCounters,
}

impl VersionAnalysis for Ssa {
    fn init_parameter(&mut self, var: i32, _catch: bool) -> i32 {
        self.counters.next(var)
    }

    fn init_write(&mut self, _ir: &Ir, _stat: StatId, pair: Version) -> i32 {
        if pair.version != 0 {
            pair.version
        } else {
            self.counters.next(pair.var)
        }
    }

    fn read_single(
        &mut self,
        _ir: &Ir,
        _stat: StatId,
        _pair: Version,
        last: i32,
        _map: &mut VersionMap,
        _live: bool,
    ) -> i32 {
        last
    }

    fn read_multiple(
        &mut self,
        _ir: &Ir,
        _stat: StatId,
        pair: Version,
        reaching: Versions,
        map: &mut VersionMap,
        _live: bool,
    ) -> i32 {
        let existing = if pair.version == 0 {
            None
        } else {
            self.phi.get_mut(&pair)
        };
        let version = if let Some(existing) = existing {
            existing.union(&reaching);
            pair.version
        } else {
            let next = self.counters.next(pair.var);
            self.phi.insert(Version::new(pair.var, next), reaching);
            next
        };
        map.set_current(pair.var, version);
        version
    }
}

impl Ssa {
    /// VarVersionsProcessor.mergePhiVersions maps every member of each
    /// connected component to its minimum version, including non-phi inputs.
    pub(crate) fn phi_representatives(&self) -> JHashMap<Version, i32> {
        let mut lookup = self.simple_reverse_phi_lookup();
        for (&key, inputs) in self.phi.iter() {
            let minimum = representative(&lookup, key).version;
            for version in inputs {
                lookup.insert(Version::new(key.var, version), minimum);
            }
        }
        lookup
    }

    /// `getSimpleReversePhiLookup`: join the phi inputs at their lowest
    /// version and flatten the representative of every phi definition.
    pub fn simple_reverse_phi_lookup(&self) -> JHashMap<Version, i32> {
        let mut representatives = JHashMap::new();
        for (&pair, inputs) in self.phi.iter() {
            let mut left = representative(&representatives, pair);
            for version in inputs {
                let right = representative(&representatives, Version::new(pair.var, version));
                if right.version < left.version {
                    representatives.insert(left, right.version);
                    left = right;
                } else if left.version < right.version {
                    representatives.insert(right, left.version);
                }
            }
        }

        for &pair in self.phi.keys() {
            representatives.insert(pair, representative(&representatives, pair).version);
        }

        representatives
    }
}

fn representative(lookup: &JHashMap<Version, i32>, mut pair: Version) -> Version {
    while let Some(&version) = lookup.get(&pair) {
        if version == pair.version {
            break;
        }
        pair.version = version;
    }
    pair
}
