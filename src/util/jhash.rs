//! Maps and sets that iterate in the order of `java.util.HashMap`.
//!
//! Vineflower sometimes depends on the iteration order of hash collections
//! keyed by integers, strings, or other value-hashed objects. The table keeps
//! both the bucket order and a separate lookup index. Tree bins keep the
//! red-black links and the iteration chain independently, as in JDK 17. The
//! last tie-break between equal-hash keys of the same class that compare as
//! equal is their JVM identity hash. A stable arena handle or the stored
//! key's insertion serial models identity when the JVM hash is unavailable.

use std::borrow::Borrow;
use std::cmp::Ordering;
use std::hash::Hash;
use std::sync::Arc;

use indexmap::IndexMap;
use itertools::{Either, Itertools};
use rustc_hash::FxBuildHasher;

mod tree;

use tree::{Bucket, TreeBin};

/// `Object.hashCode()` for the key types stored in upstream's hash collections.
pub trait JavaHash {
    fn java_hash(&self) -> i32;

    /// `HashMap.compareComparables` for Java classes implementing
    /// `Comparable<TheirOwnClass>`.
    fn java_cmp(&self, _other: &Self) -> Option<Ordering> {
        None
    }

    /// Used only for equal-hash keys with no comparative order. A homogeneous
    /// Rust key type needs only a common name. Heterogeneous representations
    /// use the actual Java class name, with `None` representing null.
    fn java_class_name(&self) -> Option<&'static str> {
        Some(std::any::type_name::<Self>())
    }

    /// A stable identity for keys that already model an upstream object
    /// handle. Other keys receive a serial when entered into the map.
    fn java_identity(&self) -> Option<u64> {
        None
    }
}

impl JavaHash for i32 {
    fn java_hash(&self) -> i32 {
        *self
    }

    fn java_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl JavaHash for i64 {
    fn java_hash(&self) -> i32 {
        (*self ^ (*self as u64 >> 32) as i64) as i32
    }

    fn java_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl JavaHash for bool {
    fn java_hash(&self) -> i32 {
        if *self { 1231 } else { 1237 }
    }

    fn java_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl JavaHash for str {
    fn java_hash(&self) -> i32 {
        self.encode_utf16().fold(0i32, |hash, unit| {
            hash.wrapping_mul(31).wrapping_add(i32::from(unit))
        })
    }

    fn java_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.encode_utf16().cmp(other.encode_utf16()))
    }
}

impl JavaHash for String {
    fn java_hash(&self) -> i32 {
        self.as_str().java_hash()
    }

    fn java_cmp(&self, other: &Self) -> Option<Ordering> {
        self.as_str().java_cmp(other.as_str())
    }
}

impl JavaHash for arcstr::ArcStr {
    fn java_hash(&self) -> i32 {
        self.as_str().java_hash()
    }

    fn java_cmp(&self, other: &Self) -> Option<Ordering> {
        self.as_str().java_cmp(other.as_str())
    }
}

impl JavaHash for Arc<str> {
    fn java_hash(&self) -> i32 {
        self.as_ref().java_hash()
    }

    fn java_cmp(&self, other: &Self) -> Option<Ordering> {
        self.as_ref().java_cmp(other.as_ref())
    }
}

impl<T: JavaHash + ?Sized> JavaHash for &T {
    fn java_hash(&self) -> i32 {
        (**self).java_hash()
    }

    fn java_cmp(&self, other: &Self) -> Option<Ordering> {
        (**self).java_cmp(*other)
    }

    fn java_class_name(&self) -> Option<&'static str> {
        (**self).java_class_name()
    }

    fn java_identity(&self) -> Option<u64> {
        (**self).java_identity()
    }
}

/// A `null` key hashes to zero.
impl<T: JavaHash> JavaHash for Option<T> {
    fn java_hash(&self) -> i32 {
        self.as_ref().map_or(0, JavaHash::java_hash)
    }

    fn java_cmp(&self, other: &Self) -> Option<Ordering> {
        self.as_ref()?.java_cmp(other.as_ref()?)
    }

    fn java_class_name(&self) -> Option<&'static str> {
        self.as_ref()?.java_class_name()
    }

    fn java_identity(&self) -> Option<u64> {
        self.as_ref()?.java_identity()
    }
}

/// `HashMap.hash`: fold the high half into the bits that select a bucket.
fn spread(hash: i32) -> i32 {
    hash ^ ((hash as u32 >> 16) as i32)
}

/// `HashMap.tableSizeFor`.
fn table_size_for(capacity: usize) -> usize {
    capacity.clamp(1, MAXIMUM_CAPACITY).next_power_of_two()
}

#[derive(Clone, Debug)]
struct Entry<V> {
    hash: i32,
    serial: u32,
    value: V,
}

type Entries<K, V> = IndexMap<K, Entry<V>, FxBuildHasher>;

/// A `java.util.HashMap` with respect to iteration order.
#[derive(Clone, Debug)]
pub struct JHashMap<K, V> {
    entries: Entries<K, V>,
    buckets: Vec<Bucket>,
    threshold: usize,
    next_serial: u32,
    swapped_entries: bool,
}

impl<K, V> Default for JHashMap<K, V> {
    fn default() -> Self {
        Self {
            entries: IndexMap::default(),
            buckets: Vec::new(),
            threshold: 0,
            next_serial: 0,
            swapped_entries: false,
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

    /// `new HashMap<>(other)` and Java's `HashMap.clone()` both reinsert the
    /// entries into a newly sized table. Rust's `Clone` preserves the table.
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

    fn bucket(&self, hash: i32) -> usize {
        hash as usize & (self.buckets.len() - 1)
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

        let old_buckets =
            std::mem::replace(&mut self.buckets, vec![Bucket::default(); new_capacity]);
        for (index, bucket) in old_buckets.into_iter().enumerate() {
            let (low, high) = bucket.split(old_capacity, &self.entries);
            self.buckets[index] = low;
            self.buckets[index + old_capacity] = high;
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
        self.insert_new(key, value, false);
        if self.entries.len() > self.threshold {
            self.resize();
        }
        None
    }

    /// `computeIfAbsent` for a mapping function that returns a value.
    pub fn get_or_insert_with(&mut self, key: K, value: impl FnOnce() -> V) -> &mut V {
        // A previous compute can leave the size one entry above the threshold.
        if self.buckets.is_empty() || self.entries.len() > self.threshold {
            self.resize();
        }
        let index = match self.entries.get_index_of(&key) {
            Some(index) => index,
            None => self.insert_new(key, value(), true),
        };
        &mut self.entries[index].value
    }

    fn insert_new(&mut self, key: K, value: V, compute: bool) -> usize {
        if self.next_serial == u32::MAX {
            // There can be at most i32::MAX live entries. Compact the serials
            // while preserving every relative order used by the trees.
            for (serial, entry) in self
                .entries
                .values_mut()
                .sorted_by_key(|entry| entry.serial)
                .enumerate()
            {
                entry.serial = serial as u32;
            }
            self.next_serial = self.entries.len() as u32;
        }
        let hash = spread(key.java_hash());
        let slot = self.bucket(hash);
        let (index, old) = self.entries.insert_full(
            key,
            Entry {
                hash,
                serial: self.next_serial,
                value,
            },
        );
        debug_assert!(old.is_none());
        self.next_serial += 1;
        let chain = match &mut self.buckets[slot] {
            Bucket::List(chain) => chain,
            Bucket::Tree(tree) => {
                tree.insert(index, &self.entries);
                return index;
            }
        };
        let treeify = chain.len() >= TREEIFY_THRESHOLD - usize::from(compute);
        if compute {
            chain.insert(0, index);
        } else {
            chain.push(index);
        }
        if treeify {
            if self.buckets.len() < MIN_TREEIFY_CAPACITY {
                self.resize();
            } else {
                let Bucket::List(chain) = std::mem::take(&mut self.buckets[slot]) else {
                    unreachable!();
                };
                self.buckets[slot] = TreeBin::from_chain(chain, &self.entries);
            }
        }
        index
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
        let (index, _, entry) = self.entries.swap_remove_full(key)?;
        self.unlink(index, entry.hash, true);
        Some(entry.value)
    }

    /// Update the removed entry's bin and the bin of the last dense entry,
    /// which now occupies the vacant index.
    fn unlink(&mut self, index: usize, hash: i32, movable: bool) {
        let bucket = self.bucket(hash);
        self.buckets[bucket].remove(index, movable);
        let old_index = self.entries.len();
        if index != old_index {
            let moved_bucket = self.bucket(self.entries[index].hash);
            self.buckets[moved_bucket].replace_index(old_index, index);
            self.swapped_entries = true;
        }
    }

    /// Removal through an iterator or `removeIf`. The current tree root
    /// need not become the first entry and a nonempty bin stays treeified.
    pub fn retain(&mut self, mut keep: impl FnMut(&K, &mut V) -> bool) {
        let mut keep_entry = |entries: &mut Entries<K, V>, index| {
            let (key, entry) = entries.get_index_mut(index).unwrap();
            keep(key, &mut entry.value)
        };
        for bucket in 0..self.buckets.len() {
            match &self.buckets[bucket] {
                Bucket::List(_) => {
                    let mut position = 0;
                    while let Bucket::List(chain) = &self.buckets[bucket] {
                        let Some(&index) = chain.get(position) else {
                            break;
                        };
                        if keep_entry(&mut self.entries, index) {
                            position += 1;
                        } else {
                            let (_, entry) = self.entries.swap_remove_index(index).unwrap();
                            self.unlink(index, entry.hash, false);
                        }
                    }
                }
                Bucket::Tree(tree) => {
                    let mut current = tree.head();
                    while let Some(index) = current {
                        let Bucket::Tree(tree) = &self.buckets[bucket] else {
                            unreachable!();
                        };
                        current = tree.next(index);
                        if !keep_entry(&mut self.entries, index) {
                            let (_, entry) = self.entries.swap_remove_index(index).unwrap();
                            self.unlink(index, entry.hash, false);
                            if current == Some(self.entries.len()) {
                                current = Some(index);
                            }
                        }
                    }
                }
            }
        }
    }

    /// `clear` empties the buckets and keeps the table.
    pub fn clear(&mut self) {
        self.entries.clear();
        self.buckets.fill_with(Bucket::default);
        self.next_serial = 0;
        self.swapped_entries = false;
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub fn iter(&self) -> impl Iterator<Item = (&K, &V)> {
        self.buckets.iter().flat_map(Bucket::indices).map(|index| {
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
        let values = self.entries.values_mut();
        let ordered = if self.swapped_entries {
            Either::Left(values.sorted_by_key(|entry| entry.serial))
        } else {
            Either::Right(values)
        };
        ordered.map(|entry| &mut entry.value)
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
        // AbstractSet.removeAll chooses key removal or iterator removal
        // depending on the relative sizes.
        if self.len() > other.len() {
            for element in other.iter() {
                self.remove(element);
            }
        } else {
            self.retain(|element| !other.contains(element));
        }
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
