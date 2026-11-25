// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! `util.collections.PackedMap`: the element table of a `FastSparseSetFactory`.

use std::fmt::Debug;
use std::hash::Hash;

use rustc_hash::FxHashMap;

/// Keys in the order they were first added, each with a packed pair of ints.
///
/// Error checking is mostly not implemented, it is up to the caller to
/// validate the input.
#[derive(Clone, Debug)]
pub struct PackedMap<K> {
    values: Vec<i64>,
    keys: Vec<K>,
    map_keys: FxHashMap<K, usize>,
}

impl<K> Default for PackedMap<K> {
    fn default() -> Self {
        Self {
            values: Vec::new(),
            keys: Vec::new(),
            map_keys: FxHashMap::default(),
        }
    }
}

impl<K: Hash + Eq + Clone> PackedMap<K> {
    pub fn new() -> Self {
        Self::default()
    }

    /// `putWithKey(high, low, key)`: stores the packed pair and returns it.
    pub fn put_with_key_parts(&mut self, high: i32, low: i32, key: K) -> i64 {
        let packed = pack(high, low);
        self.put_with_key(packed, key);
        packed
    }

    /// Sets the value of `key`; a new key takes the next index.
    pub fn put_with_key(&mut self, element: i64, key: K) {
        match self.map_keys.get(&key) {
            Some(&index) => self.values[index] = element,
            None => {
                self.map_keys.insert(key.clone(), self.keys.len());
                self.values.push(element);
                self.keys.push(key);
            }
        }
    }

    pub fn contains_key(&self, key: &K) -> bool {
        self.map_keys.contains_key(key)
    }

    pub fn get_with_key(&self, key: &K) -> i64
    where
        K: Debug,
    {
        match self.map_keys.get(key) {
            Some(&index) => self.values[index],
            None => panic!(
                "Key not found: {key:?} in key map. Use containsKey to check if it exists first!"
            ),
        }
    }

}

pub fn pack(high: i32, low: i32) -> i64 {
    i64::from(low as u32) | i64::from(high as u32) << 32
}

pub fn unpack_low(packed: i64) -> i32 {
    packed as i32
}

pub fn unpack_high(packed: i64) -> i32 {
    (packed >> 32) as i32
}

impl<K> PackedMap<K> {
    pub fn get(&self, index: usize) -> i64 {
        self.values[index]
    }

    pub fn get_key(&self, index: usize) -> &K {
        &self.keys[index]
    }

    pub fn size(&self) -> usize {
        self.keys.len()
    }
}
