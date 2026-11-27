//! Reaching-version maps for locals, stack variables and tracked fields.

use std::collections::BTreeMap;
use std::collections::btree_map::Entry;
use std::fmt;

use crate::decompiler::exps::STACK_BASE;
use crate::util::fast_sparse_set::{FastSparseSet, FastSparseSetFactory};

pub type Versions = FastSparseSet<i32>;

/// `SFormsFastMapDirect`, with sparse storage within each variable domain.
#[derive(Clone)]
pub struct VersionMap {
    factory: FastSparseSetFactory<i32>,
    fields: BTreeMap<i32, Versions>,
    stacks: BTreeMap<i32, Versions>,
    locals: BTreeMap<i32, Versions>,
}

impl VersionMap {
    pub fn new(factory: &FastSparseSetFactory<i32>) -> Self {
        Self {
            factory: factory.clone(),
            fields: BTreeMap::new(),
            stacks: BTreeMap::new(),
            locals: BTreeMap::new(),
        }
    }

    pub fn len(&self) -> usize {
        self.locals.len() + self.stacks.len() + self.fields.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn get(&self, key: i32) -> Option<&Versions> {
        self.domain(key).get(&key)
    }

    pub fn get_mut(&mut self, key: i32) -> Option<&mut Versions> {
        self.domain_mut(key).get_mut(&key)
    }

    pub fn put(&mut self, key: i32, versions: Versions) {
        self.domain_mut(key).insert(key, versions);
    }

    pub fn remove(&mut self, key: i32) -> Option<Versions> {
        self.domain_mut(key).remove(&key)
    }

    pub(crate) fn retain(&mut self, mut keep: impl FnMut(i32, &mut Versions) -> bool) {
        for domain in [&mut self.fields, &mut self.stacks, &mut self.locals] {
            domain.retain(|&key, versions| keep(key, versions));
        }
    }

    pub fn set_current(&mut self, var: i32, version: i32) {
        let mut set = self.factory.create_empty_set();
        set.add(version);
        self.put(var, set);
    }

    pub fn clear_fields(&mut self) {
        self.fields.clear();
    }

    pub fn clear_stacks(&mut self) {
        self.stacks.clear();
    }

    /// Throwing clears the operand stack and invalidates tracked field reads.
    pub(super) fn catchable_locals(&self) -> Self {
        Self {
            locals: self.locals.clone(),
            ..Self::new(&self.factory)
        }
    }

    pub fn union(&mut self, other: &Self) {
        for (key, versions) in other.iter() {
            match self.domain_mut(key).entry(key) {
                Entry::Occupied(mut slot) => slot.get_mut().union(versions),
                Entry::Vacant(slot) => {
                    slot.insert(versions.clone());
                }
            }
        }
    }

    pub fn intersection(&mut self, other: &Self) {
        for domain in [&mut self.fields, &mut self.stacks, &mut self.locals] {
            domain.retain(|&key, versions| {
                let Some(overlap) = other.get(key) else {
                    return false;
                };
                versions.intersection(overlap);
                !versions.is_empty()
            });
        }
    }

    pub fn complement(&mut self, other: &Self) {
        for domain in [&mut self.fields, &mut self.stacks, &mut self.locals] {
            domain.retain(|&key, versions| {
                let Some(removed) = other.get(key) else {
                    return true;
                };
                versions.complement(removed);
                !versions.is_empty()
            });
        }
    }

    /// `entryList()`: fields by increasing absolute index, then stack
    /// variables and locals, each in increasing index order.
    pub fn iter(&self) -> impl Iterator<Item = (i32, &Versions)> {
        self.fields
            .iter()
            .rev()
            .chain(&self.stacks)
            .chain(&self.locals)
            .map(|(&key, versions)| (key, versions))
    }

    fn domain(&self, key: i32) -> &BTreeMap<i32, Versions> {
        if key < 0 {
            &self.fields
        } else if key >= STACK_BASE {
            &self.stacks
        } else {
            &self.locals
        }
    }

    fn domain_mut(&mut self, key: i32) -> &mut BTreeMap<i32, Versions> {
        if key < 0 {
            &mut self.fields
        } else if key >= STACK_BASE {
            &mut self.stacks
        } else {
            &mut self.locals
        }
    }
}

impl fmt::Debug for VersionMap {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl PartialEq for VersionMap {
    fn eq(&self, other: &Self) -> bool {
        self.locals == other.locals && self.stacks == other.stacks && self.fields == other.fields
    }
}

impl Eq for VersionMap {}

/// The maps for a normal expression or for the two outcomes of a condition.
#[derive(Debug)]
pub struct VarMapHolder {
    if_true: VersionMap,
    if_false: Option<VersionMap>,
}

impl VarMapHolder {
    pub fn normal(map: VersionMap) -> Self {
        Self {
            if_true: map,
            if_false: None,
        }
    }

    pub fn is_normal(&self) -> bool {
        self.if_false.is_none()
    }

    pub fn if_true(&self) -> &VersionMap {
        &self.if_true
    }

    pub fn if_false(&self) -> &VersionMap {
        self.if_false.as_ref().unwrap_or(&self.if_true)
    }

    /// Split a normal map before writing a condition's true outcome.
    pub(super) fn true_branch_mut(&mut self) -> &mut VersionMap {
        self.if_false.get_or_insert_with(|| self.if_true.clone());
        &mut self.if_true
    }

    pub fn normal_mut(&mut self) -> &mut VersionMap {
        assert!(self.is_normal(), "variable map is split");
        &mut self.if_true
    }

    pub fn merge_branches(&mut self) -> &mut VersionMap {
        if let Some(if_false) = self.if_false.take() {
            self.if_true.union(&if_false);
        }
        &mut self.if_true
    }

    /// Keep one outcome in this holder as a normal map and move the other
    /// outcome to the caller. Only an unsplit condition needs a copy.
    pub fn take_alternative(&mut self, keep_true: bool) -> VersionMap {
        let if_false = self.if_false.take().unwrap_or_else(|| self.if_true.clone());
        if keep_true {
            if_false
        } else {
            std::mem::replace(&mut self.if_true, if_false)
        }
    }

    pub fn merge_outcome(&mut self, when_true: bool, other: &VersionMap) {
        if other.is_empty() {
            return;
        }
        let if_false = self.if_false.get_or_insert_with(|| self.if_true.clone());
        if when_true {
            self.if_true.union(other);
        } else {
            if_false.union(other);
        }
    }

    /// Combine the two arms of a conditional expression, retaining their
    /// distinct true and false outputs when either arm produced a split.
    pub fn merge_ternary(&mut self, mut then_arm: Self) {
        if !self.is_normal() {
            self.merge_outcome(true, then_arm.if_true());
            self.merge_outcome(false, then_arm.if_false());
        } else if then_arm.is_normal() {
            self.if_true.union(&then_arm.if_true);
        } else {
            then_arm.merge_outcome(true, &self.if_true);
            then_arm.merge_outcome(false, &self.if_true);
            *self = then_arm;
        }
    }

    pub fn swap(&mut self) {
        if let Some(if_false) = &mut self.if_false {
            std::mem::swap(&mut self.if_true, if_false);
        }
    }
}
