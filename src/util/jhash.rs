// SPDX-License-Identifier: Apache-2.0

//! Maps and sets that iterate in the order of `java.util.HashMap`.
//!
//! Vineflower sometimes depends on the iteration order of hash collections
//! keyed by integers, strings, or other value-hashed objects. The table keeps
//! both the indices in each `HashMap` bucket and the entries they refer to.
//!
//! The bucket chains follow JDK 17 through insertion, removal and resize. At
//! capacities where the JDK would turn a chain into a tree, the chain remains
//! a list, so iteration can differ from Java for those buckets.

use std::borrow::Borrow;
use std::hash::Hash;
use std::sync::Arc;

use indexmap::IndexMap;
use rustc_hash::FxBuildHasher;

/// `Object.hashCode()` for the key types stored in upstream's hash collections.
pub trait JavaHash {
    fn java_hash(&self) -> i32;
}

impl JavaHash for i32 {
    fn java_hash(&self) -> i32 {
        *self
    }
}

impl JavaHash for i64 {
    fn java_hash(&self) -> i32 {
        (*self ^ (*self as u64 >> 32) as i64) as i32
    }
}

impl JavaHash for bool {
    fn java_hash(&self) -> i32 {
        if *self { 1231 } else { 1237 }
    }
}

impl JavaHash for str {
    fn java_hash(&self) -> i32 {
        self.encode_utf16().fold(0i32, |hash, unit| {
            hash.wrapping_mul(31).wrapping_add(i32::from(unit))
        })
    }
}

impl JavaHash for String {
    fn java_hash(&self) -> i32 {
        self.as_str().java_hash()
    }
}

impl JavaHash for arcstr::ArcStr {
    fn java_hash(&self) -> i32 {
        self.as_str().java_hash()
    }
}

impl JavaHash for Arc<str> {
    fn java_hash(&self) -> i32 {
        self.as_ref().java_hash()
    }
}

impl<T: JavaHash + ?Sized> JavaHash for &T {
    fn java_hash(&self) -> i32 {
        (**self).java_hash()
    }
}

/// A `null` key hashes to zero.
impl<T: JavaHash> JavaHash for Option<T> {
    fn java_hash(&self) -> i32 {
        self.as_ref().map_or(0, JavaHash::java_hash)
    }
}

/// `HashMap.hash`: fold the high half into the bits that select a bucket.
fn spread(hash: i32) -> u32 {
    let hash = hash as u32;
    hash ^ (hash >> 16)
}

/// `HashMap.tableSizeFor`.
fn table_size_for(capacity: usize) -> usize {
    capacity.clamp(1, MAXIMUM_CAPACITY).next_power_of_two()
}

#[derive(Clone, Debug)]
struct Entry<V> {
    hash: usize,
    value: V,
}

/// A `java.util.HashMap` with respect to iteration order.
#[derive(Clone, Debug)]
pub struct JHashMap<K, V> {
    entries: IndexMap<K, Entry<V>, FxBuildHasher>,
    /// Entry indices in chain order, by bucket number.
    buckets: Vec<Vec<usize>>,
    threshold: usize,
}

impl<K, V> Default for JHashMap<K, V> {
    fn default() -> Self {
        Self {
            entries: IndexMap::default(),
            buckets: Vec::new(),
            threshold: 0,
        }
    }
}

const DEFAULT_INITIAL_CAPACITY: usize = 16;
const MAXIMUM_CAPACITY: usize = 1 << 30;
const TREEIFY_THRESHOLD: usize = 8;
const MIN_TREEIFY_CAPACITY: usize = 64;

impl<K: JavaHash + Hash + Eq, V> JHashMap<K, V> {
    /// `new HashMap<>()`.
    pub fn new() -> Self {
        Self::default()
    }

    /// `new HashMap<>(initialCapacity)`.
    pub fn with_capacity(initial_capacity: usize) -> Self {
        Self {
            threshold: table_size_for(initial_capacity),
            ..Self::default()
        }
    }

    /// `new HashMap<>(other)`: the copy sizes its own table, so it may iterate
    /// in a different order than `other`. `clone()` keeps the table instead.
    pub fn copy_of(other: &Self) -> Self
    where
        K: Clone,
        V: Clone,
    {
        let mut copy = Self::new();
        copy.put_all(
            other
                .iter()
                .map(|(key, value)| (key.clone(), value.clone())),
            other.len(),
        );
        copy
    }

    /// `putAll` for a source of `len` entries, visited in the source's order.
    pub fn put_all(&mut self, entries: impl IntoIterator<Item = (K, V)>, len: usize) {
        if len == 0 {
            return;
        }
        if self.buckets.is_empty() {
            let wanted = (len as f32 / 0.75 + 1.0) as usize;
            if wanted > self.threshold {
                self.threshold = table_size_for(wanted);
            }
        } else {
            while len > self.threshold && self.buckets.len() < MAXIMUM_CAPACITY {
                self.resize();
            }
        }
        for (key, value) in entries {
            self.insert(key, value);
        }
    }

    fn bucket(&self, hash: usize) -> usize {
        hash & (self.buckets.len() - 1)
    }

    fn resize(&mut self) {
        let old_capacity = self.buckets.len();
        let new_capacity = match (old_capacity, self.threshold) {
            (0, 0) => DEFAULT_INITIAL_CAPACITY,
            (0, initial_capacity) => initial_capacity,
            (MAXIMUM_CAPACITY, _) => {
                self.threshold = i32::MAX as usize;
                return;
            }
            (capacity, _) => capacity * 2,
        };
        self.threshold = match (old_capacity, new_capacity) {
            (_, MAXIMUM_CAPACITY) => i32::MAX as usize,
            (old, _) if old >= DEFAULT_INITIAL_CAPACITY => self.threshold * 2,
            _ => new_capacity * 3 / 4,
        };

        let old_buckets = std::mem::replace(&mut self.buckets, vec![Vec::new(); new_capacity]);
        // Each old chain splits between its low and high buckets. Appending
        // in chain order keeps both halves stable.
        for index in old_buckets.into_iter().flatten() {
            let hash = self.entries[index].hash;
            let bucket = self.bucket(hash);
            self.buckets[bucket].push(index);
        }
    }

    /// `put`: returns the previous value. A replaced key keeps its position.
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        if self.buckets.is_empty() {
            self.resize();
        }
        if let Some(slot) = self.entries.get_mut(&key) {
            return Some(std::mem::replace(&mut slot.value, value));
        }
        let hash = spread(key.java_hash()) as usize;
        let bucket = self.bucket(hash);
        let overlong = self.buckets[bucket].len() >= TREEIFY_THRESHOLD;
        let index = self.entries.len();
        self.entries.insert(key, Entry { hash, value });
        self.buckets[bucket].push(index);
        self.resize_long_chain(overlong);
        if self.entries.len() > self.threshold {
            self.resize();
        }
        None
    }

    fn resize_long_chain(&mut self, overlong: bool) {
        // The JDK grows a small table before allowing a bucket to become a tree.
        if overlong && self.buckets.len() < MIN_TREEIFY_CAPACITY {
            self.resize();
        }
    }

    /// `computeIfAbsent`.
    pub fn get_or_insert_with(&mut self, key: K, value: impl FnOnce() -> V) -> &mut V
    where
        K: Clone,
    {
        // This check also happens when the key is already present. A previous
        // compute can leave the size one entry above the threshold.
        if self.buckets.is_empty() || self.entries.len() > self.threshold {
            self.resize();
        }
        let index = match self.entries.get_index_of(&key) {
            Some(index) => index,
            None => {
                let hash = spread(key.java_hash()) as usize;
                let bucket = self.bucket(hash);
                let overlong = self.buckets[bucket].len() >= TREEIFY_THRESHOLD - 1;
                let index = self.entries.len();
                self.entries.insert(
                    key,
                    Entry {
                        hash,
                        value: value(),
                    },
                );
                self.buckets[bucket].insert(0, index);
                self.resize_long_chain(overlong);
                index
            }
        };
        &mut self.entries[index].value
    }

    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.entries.get(key).map(|entry| &entry.value)
    }

    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.entries.get_mut(key).map(|entry| &mut entry.value)
    }

    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.entries.contains_key(key)
    }

    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let (index, _key, entry) = self.entries.shift_remove_full(key)?;
        let bucket = self.bucket(entry.hash);
        self.buckets[bucket].retain(|&position| position != index);
        for position in self.buckets.iter_mut().flatten() {
            *position -= usize::from(*position > index);
        }
        Some(entry.value)
    }

    /// Removal through an iterator or `removeIf`; the table is left alone.
    pub fn retain(&mut self, mut keep: impl FnMut(&K, &mut V) -> bool) {
        let mut retained = vec![false; self.entries.len()];
        for &index in self.buckets.iter().flatten() {
            let (key, entry) = self.entries.get_index_mut(index).unwrap();
            retained[index] = keep(key, &mut entry.value);
        }

        let mut next_position = 0;
        let positions = retained
            .into_iter()
            .map(|keep| {
                let position = keep.then_some(next_position);
                next_position += usize::from(keep);
                position
            })
            .collect::<Vec<_>>();
        let mut old_positions = positions.iter();
        self.entries
            .retain(|_, _| old_positions.next().unwrap().is_some());
        for bucket in &mut self.buckets {
            bucket.retain_mut(|index| match positions[*index] {
                Some(position) => {
                    *index = position;
                    true
                }
                None => false,
            });
        }
    }

    /// `clear` empties the buckets and keeps the table.
    pub fn clear(&mut self) {
        self.entries.clear();
        self.buckets.fill_with(Vec::new);
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub fn iter(&self) -> impl Iterator<Item = (&K, &V)> {
        self.buckets.iter().flatten().map(|&index| {
            let (key, entry) = self.entries.get_index(index).unwrap();
            (key, &entry.value)
        })
    }

    pub fn keys(&self) -> impl Iterator<Item = &K> {
        self.iter().map(|(key, _)| key)
    }

    pub fn values(&self) -> impl Iterator<Item = &V> {
        self.iter().map(|(_, value)| value)
    }

    /// Values in insertion order, for updates that do not depend on the order.
    pub fn values_mut(&mut self) -> impl Iterator<Item = &mut V> {
        self.entries.values_mut().map(|entry| &mut entry.value)
    }
}

impl<K: JavaHash + Hash + Eq, V: PartialEq> PartialEq for JHashMap<K, V> {
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len()
            && self
                .entries
                .iter()
                .all(|(key, entry)| other.get(key) == Some(&entry.value))
    }
}

impl<K: JavaHash + Hash + Eq, V: Eq> Eq for JHashMap<K, V> {}

/// A `java.util.HashSet` with respect to iteration order.
#[derive(Clone, Debug)]
pub struct JHashSet<T>(JHashMap<T, ()>);

impl<T> Default for JHashSet<T> {
    fn default() -> Self {
        Self(JHashMap::default())
    }
}

impl<T: JavaHash + Hash + Eq> JHashSet<T> {
    /// `new HashSet<>()`.
    pub fn new() -> Self {
        Self::default()
    }

    /// `new HashSet<>(initialCapacity)`.
    pub fn with_capacity(initial_capacity: usize) -> Self {
        Self(JHashMap::with_capacity(initial_capacity))
    }

    /// `new HashSet<>(collection)` for a collection of `len` elements.
    pub fn from_collection(elements: impl IntoIterator<Item = T>, len: usize) -> Self {
        let mut set = Self::with_capacity(((len as f32 / 0.75) as usize + 1).max(16));
        set.extend(elements);
        set
    }

    /// `new HashSet<>(other)`.
    pub fn copy_of(other: &Self) -> Self
    where
        T: Clone,
    {
        Self::from_collection(other.iter().cloned(), other.len())
    }

    /// `add`: true when the element was not present.
    pub fn insert(&mut self, element: T) -> bool {
        self.0.insert(element, ()).is_none()
    }

    pub fn contains<Q>(&self, element: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.0.contains_key(element)
    }

    pub fn remove<Q>(&mut self, element: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.0.remove(element).is_some()
    }

    pub fn retain(&mut self, mut keep: impl FnMut(&T) -> bool) {
        self.0.retain(|element, ()| keep(element));
    }

    /// `retainAll`.
    pub fn retain_all(&mut self, other: &Self) {
        self.retain(|element| other.contains(element));
    }

    /// `removeAll`.
    pub fn remove_all(&mut self, other: &Self) {
        self.retain(|element| !other.contains(element));
    }

    pub fn clear(&mut self) {
        self.0.clear();
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.0.keys()
    }
}

/// `addAll`.
impl<T: JavaHash + Hash + Eq> Extend<T> for JHashSet<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, elements: I) {
        for element in elements {
            self.insert(element);
        }
    }
}

impl<T: JavaHash + Hash + Eq> PartialEq for JHashSet<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<T: JavaHash + Hash + Eq> Eq for JHashSet<T> {}
