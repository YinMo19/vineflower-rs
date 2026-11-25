// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! `util.collections.VBStyleCollection`: a list whose elements can also be
//! looked up by key.

use std::borrow::Borrow;
use std::fmt::Display;
use std::hash::Hash;
use std::ops::{Deref, DerefMut, Index, IndexMut};
use std::slice::SliceIndex;

use itertools::Itertools;
use rustc_hash::{FxBuildHasher, FxHashMap};

/// An ordered list with a key-to-index lookup.
///
/// Reading, iterating and replacing elements in place work as on a slice.
/// Everything that changes the length goes through the methods below, which
/// keep the keys aligned with the elements. An element added without a key has
/// `None` in [`lst_keys`](Self::lst_keys).
///
/// Keys are meant to be unique, but nothing enforces it: a lookup follows the
/// position recorded last for the key, and removing any element that carries
/// the key drops the key from the lookup.
#[derive(Clone, Debug)]
pub struct VBStyleCollection<E, K> {
    elements: Vec<E>,
    map: FxHashMap<K, usize>,
    lst_keys: Vec<Option<K>>,
}

impl<E, K> VBStyleCollection<E, K> {
    pub fn new() -> Self {
        Self {
            elements: Vec::new(),
            map: FxHashMap::default(),
            lst_keys: Vec::new(),
        }
    }

    pub fn with_capacity(initial_capacity: usize) -> Self {
        Self {
            elements: Vec::with_capacity(initial_capacity),
            map: FxHashMap::with_capacity_and_hasher(initial_capacity, FxBuildHasher),
            lst_keys: Vec::with_capacity(initial_capacity),
        }
    }

    /// `add(element)`: appends an element that has no key.
    pub fn push(&mut self, element: E) {
        self.lst_keys.push(None);
        self.elements.push(element);
    }

    /// `remove(Object)`, which upstream never implemented.
    pub fn remove_element(&mut self, _element: &E) -> bool {
        panic!("not implemented!")
    }

    pub fn get_last(&self) -> &E {
        self.elements.last().unwrap()
    }

    pub fn clear(&mut self) {
        self.map.clear();
        self.lst_keys.clear();
        self.elements.clear();
    }

    /// The key of the element at `index`, if it was added with one.
    pub fn get_key(&self, index: usize) -> Option<&K> {
        self.lst_keys[index].as_ref()
    }

    /// The key of every element, in list order.
    pub fn lst_keys(&self) -> &[Option<K>] {
        &self.lst_keys
    }

    pub fn to_string_vb(&self) -> String
    where
        E: Display,
        K: Display,
    {
        let entries = self.elements.iter().enumerate().map(|(index, element)| {
            match &self.lst_keys[index] {
                Some(key) => format!("{key}={element}"),
                None => format!("null={element}"),
            }
        });
        format!("[{}]", entries.format(", "))
    }
}

impl<E, K: Hash + Eq + Clone> VBStyleCollection<E, K> {
    /// Appends `elements` and, independently of them, `keys`: the first key
    /// belongs to the first new position, whatever the two lengths are.
    pub fn add_all_with_key(
        &mut self,
        elements: impl IntoIterator<Item = E>,
        keys: impl IntoIterator<Item = Option<K>>,
    ) {
        let mut index = self.elements.len();
        for key in keys {
            if let Some(key) = &key {
                self.map.insert(key.clone(), index);
            }
            index += 1;
            self.lst_keys.push(key);
        }
        self.elements.extend(elements);
    }

    pub fn add_with_key(&mut self, element: E, key: K) {
        self.map.insert(key.clone(), self.elements.len());
        self.elements.push(element);
        self.lst_keys.push(Some(key));
    }

    /// Replaces the element stored under `key` and returns the old one, or
    /// appends the element if the key is new.
    pub fn put_with_key(&mut self, element: E, key: K) -> Option<E> {
        match self.map.get(&key) {
            Some(&index) => Some(std::mem::replace(&mut self.elements[index], element)),
            None => {
                self.add_with_key(element, key);
                None
            }
        }
    }

    /// `add(index, element)`: inserts an element that has no key.
    pub fn insert(&mut self, index: usize, element: E) {
        self.add_to_list_index(index, 1);
        self.lst_keys.insert(index, None);
        self.elements.insert(index, element);
    }

    pub fn add_with_key_and_index(&mut self, index: usize, element: E, key: K) {
        self.add_to_list_index(index, 1);
        self.map.insert(key.clone(), index);
        self.elements.insert(index, element);
        self.lst_keys.insert(index, Some(key));
    }

    /// Removes the element stored under `key`, if there is one.
    pub fn remove_with_key<Q>(&mut self, key: &Q)
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let Some(&index) = self.map.get(key) else {
            return;
        };
        self.add_to_list_index(index + 1, -1);
        self.elements.remove(index);
        self.lst_keys.remove(index);
        self.map.remove(key);
    }

    /// `remove(index)`.
    pub fn remove(&mut self, index: usize) -> E {
        self.add_to_list_index(index + 1, -1);
        if let Some(key) = &self.lst_keys[index] {
            self.map.remove(key);
        }
        self.lst_keys.remove(index);
        self.elements.remove(index)
    }

    pub fn get_with_key<Q>(&self, key: &Q) -> Option<&E>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.map.get(key).map(|&index| &self.elements[index])
    }

    /// `getWithKey` for an element that is modified in place.
    pub fn get_with_key_mut<Q>(&mut self, key: &Q) -> Option<&mut E>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.map.get(key).map(|&index| &mut self.elements[index])
    }

    pub fn index_of_key<Q>(&self, key: &Q) -> Option<usize>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.map.get(key).copied()
    }

    /// The position of the element stored under `key`, which must be present.
    pub fn get_index_by_key<Q>(&self, key: &Q) -> usize
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.map[key]
    }

    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.map.contains_key(key)
    }

    /// Moves the recorded position of every keyed element from `index` on.
    fn add_to_list_index(&mut self, index: usize, diff: isize) {
        for position in (index..self.lst_keys.len()).rev() {
            if let Some(key) = &self.lst_keys[position] {
                self.map.insert(key.clone(), position.wrapping_add_signed(diff));
            }
        }
    }
}

impl<E, K> Default for VBStyleCollection<E, K> {
    fn default() -> Self {
        Self::new()
    }
}

impl<E, K> Deref for VBStyleCollection<E, K> {
    type Target = [E];

    fn deref(&self) -> &[E] {
        &self.elements
    }
}

impl<E, K> DerefMut for VBStyleCollection<E, K> {
    fn deref_mut(&mut self) -> &mut [E] {
        &mut self.elements
    }
}

impl<E, K, I: SliceIndex<[E]>> Index<I> for VBStyleCollection<E, K> {
    type Output = I::Output;

    fn index(&self, index: I) -> &I::Output {
        &self.elements[index]
    }
}

impl<E, K, I: SliceIndex<[E]>> IndexMut<I> for VBStyleCollection<E, K> {
    fn index_mut(&mut self, index: I) -> &mut I::Output {
        &mut self.elements[index]
    }
}

impl<'a, E, K> IntoIterator for &'a VBStyleCollection<E, K> {
    type Item = &'a E;
    type IntoIter = std::slice::Iter<'a, E>;

    fn into_iter(self) -> Self::IntoIter {
        self.elements.iter()
    }
}

impl<'a, E, K> IntoIterator for &'a mut VBStyleCollection<E, K> {
    type Item = &'a mut E;
    type IntoIter = std::slice::IterMut<'a, E>;

    fn into_iter(self) -> Self::IntoIter {
        self.elements.iter_mut()
    }
}

/// `addAll`: appends elements that have no key.
impl<E, K> Extend<E> for VBStyleCollection<E, K> {
    fn extend<I: IntoIterator<Item = E>>(&mut self, elements: I) {
        let len = self.elements.len();
        self.elements.extend(elements);
        let added = self.elements.len() - len;
        self.lst_keys.extend(std::iter::repeat_with(|| None).take(added));
    }
}
