// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! `util.collections.FastSparseSetFactory` with its `FastSparseSet` and
//! `FastSparseSetIterator`: bit sets over elements that a shared factory
//! numbers in the order it first sees them.

use std::cell::RefCell;
use std::fmt::{self, Debug, Display};
use std::hash::Hash;
use std::rc::Rc;

use itertools::Itertools;
use smallvec::SmallVec;

use super::jhash::{JHashSet, JavaHash};
use super::packed_map::{PackedMap, unpack_high, unpack_low};

/// Assigns every element a block and a bit mask within that block.
///
/// The factory is shared with the sets it creates, and a clone is another
/// handle to the same factory.
pub struct FastSparseSetFactory<E>(Rc<RefCell<FactoryState<E>>>);

struct FactoryState<E> {
    col_values_internal: PackedMap<E>,
    last_block: i32,
    last_mask: i32,
}

impl<E: Hash + Eq + Clone + Debug> FastSparseSetFactory<E> {
    pub fn new(set: impl IntoIterator<Item = E>) -> Self {
        let mut col_values_internal = PackedMap::new();
        let mut block = -1;
        let mut mask = -1;
        for (index, element) in set.into_iter().enumerate() {
            block = (index >> 5) as i32;
            mask = if index & 31 == 0 { 1 } else { mask << 1 };
            col_values_internal.put_with_key_parts(mask, block, element);
        }
        Self(Rc::new(RefCell::new(FactoryState {
            col_values_internal,
            last_block: block,
            last_mask: mask,
        })))
    }

    pub fn create_empty_set(&self) -> FastSparseSet<E> {
        // Originally, this was the last block + 1. However, in the most common case, only 1
        // element is added, which makes the array unnecessarily large. Instead,
        // max(last block, 1) is used to ensure empty factories don't produce -1 lengths.
        let length = self.0.borrow().last_block.max(1) as usize;
        FastSparseSet {
            factory: self.clone(),
            data: SmallVec::from_elem(0, length),
            next: None,
        }
    }

    /// The packed block and mask of `element`. An element the factory has not
    /// seen is numbered here, even when a set merely tests for it or removes
    /// it, and that fixes its place in the iteration order of every set.
    fn index_of(&self, element: &E) -> i64 {
        let mut state = self.0.borrow_mut();
        if !state.col_values_internal.contains_key(element) {
            state.add_element(element.clone())
        } else {
            state.col_values_internal.get_with_key(element)
        }
    }
}

impl<E: Hash + Eq + Clone> FactoryState<E> {
    fn add_element(&mut self, element: E) -> i64 {
        if self.last_mask < 0 {
            self.last_mask = 1;
            self.last_block += 1;
        } else {
            self.last_mask <<= 1;
        }
        self.col_values_internal
            .put_with_key_parts(self.last_mask, self.last_block, element)
    }
}

impl<E> Clone for FastSparseSetFactory<E> {
    fn clone(&self) -> Self {
        Self(Rc::clone(&self.0))
    }
}

/// A set of elements of one factory.
///
/// `data` holds one 32-bit block per 32 elements. Up to four blocks fit
/// inline, so most SForms sets need no heap storage. `next` links each
/// block to the next non-empty one (0 ends the chain) and exists
/// only once a block other than the first has been used. Iteration,
/// [`union`](Self::union), [`complement`](Self::complement) and
/// [`is_empty`](Self::is_empty) trust these links.
pub struct FastSparseSet<E> {
    factory: FastSparseSetFactory<E>,
    data: SmallVec<[i32; 4]>,
    next: Option<Vec<usize>>,
}

impl<E> FastSparseSet<E> {
    fn ensure_capacity(&mut self, index: usize) {
        let mut newlength = self.data.len().max(1);
        while newlength <= index {
            newlength *= 2;
        }
        self.data.resize(newlength, 0);
        if let Some(next) = &mut self.next {
            next.resize(newlength, 0);
        }
    }

    fn get_next_idx(&self, block: usize) -> usize {
        self.next.as_ref().map_or(0, |next| next[block])
    }

    fn alloc_next(&mut self) -> &mut Vec<usize> {
        let length = self.data.len();
        self.next.get_or_insert_with(|| vec![0; length])
    }

    fn set_next(&mut self) {
        let mut link = 0;
        for i in (0..self.data.len()).rev() {
            if link != 0 && self.next.is_none() {
                self.alloc_next()[i] = link;
            }
            if self.data[i] != 0 {
                link = i;
            }
        }
    }

    fn change_next(&mut self, key: usize, oldnext: usize, newnext: usize) {
        for i in (0..key).rev() {
            if self.get_next_idx(i) != oldnext {
                break;
            }
            self.alloc_next()[i] = newnext;
        }
    }

    pub fn union(&mut self, set: &FastSparseSet<E>) {
        let intlength = self.data.len();
        let mut pointer = 0;
        loop {
            if pointer >= intlength {
                self.ensure_capacity(set.data.len() - 1);
            }

            let nextrec = self.data[pointer] == 0;
            self.data[pointer] |= set.data[pointer];

            if nextrec {
                self.change_next(pointer, self.get_next_idx(pointer), pointer);
            }

            pointer = set.get_next_idx(pointer);
            if pointer == 0 {
                break;
            }
        }
    }

    /// Keeps the elements that are also in `set`. The block links are not
    /// brought up to date afterwards (upstream's `setNext` is ineffective), so
    /// they may keep pointing at blocks this emptied.
    pub fn intersection(&mut self, set: &FastSparseSet<E>) {
        let minlength = set.data.len().min(self.data.len());
        for i in 0..minlength {
            self.data[i] &= set.data[i];
        }
        self.data[minlength..].fill(0);

        self.set_next();
    }

    /// Removes the elements of `set`.
    pub fn complement(&mut self, set: &FastSparseSet<E>) {
        let extlength = set.data.len();
        let mut pointer = 0;
        loop {
            if pointer >= extlength {
                break;
            }

            self.data[pointer] &= !set.data[pointer];
            if self.data[pointer] == 0 {
                self.change_next(pointer, pointer, self.get_next_idx(pointer));
            }

            pointer = self.get_next_idx(pointer);
            if pointer == 0 {
                break;
            }
        }
    }

    /// `getCardinality()`: 0 or 1 for a set of that size, 2 for any larger one.
    pub fn cardinality(&self) -> i32 {
        let mut found = false;
        for &block in self.data.iter().rev() {
            if block != 0 {
                if found || block.count_ones() != 1 {
                    return 2;
                }
                found = true;
            }
        }
        i32::from(found)
    }

    /// Judged by the first block and its link alone: a set that
    /// [`intersection`](Self::intersection) or [`retain`](Self::retain)
    /// emptied can still claim to have elements.
    pub fn is_empty(&self) -> bool {
        self.data.is_empty() || (self.get_next_idx(0) == 0 && self.data[0] == 0)
    }

    pub fn iter(&self) -> FastSparseSetIterator<'_, E> {
        FastSparseSetIterator { set: self, from: 0 }
    }

    /// The first element index at or after `index`, found along the block links.
    fn get_next_index(&self, index: usize) -> Option<usize> {
        let mut bindex = index >> 5;
        let mut dindex = index & 0x1F;

        while bindex < self.data.len() {
            let block = (self.data[bindex] as u32) >> dindex;
            if block != 0 {
                return Some((bindex << 5) + dindex + block.trailing_zeros() as usize);
            }

            dindex = 0;
            bindex = self.get_next_idx(bindex);
            if bindex == 0 {
                break;
            }
        }

        None
    }
}

impl<E: Hash + Eq + Clone + Debug> FastSparseSet<E> {
    pub fn add(&mut self, element: E) {
        let index = self.factory.index_of(&element);

        let block = unpack_low(index) as usize;
        if block >= self.data.len() {
            self.ensure_capacity(block);
        }

        self.data[block] |= unpack_high(index);

        self.change_next(block, self.get_next_idx(block), block);
    }

    pub fn remove(&mut self, element: &E) {
        let index = self.factory.index_of(element);

        let block = unpack_low(index) as usize;
        if block < self.data.len() {
            self.data[block] &= !unpack_high(index);

            if self.data[block] == 0 {
                self.change_next(block, block, self.get_next_idx(block));
            }
        }
    }

    pub fn contains(&self, element: &E) -> bool {
        let index = self.factory.index_of(element);

        let block = unpack_low(index) as usize;
        block < self.data.len() && self.data[block] & unpack_high(index) != 0
    }
}

impl<E: Clone> FastSparseSet<E> {
    /// What removing through upstream's iterator amounts to: drops the
    /// elements `keep` rejects without touching the block links.
    pub fn retain(&mut self, mut keep: impl FnMut(&E) -> bool) {
        let mut from = 0;
        while let Some(pointer) = self.get_next_index(from) {
            from = pointer + 1;
            let (element, index) = {
                let state = self.factory.0.borrow();
                let values = &state.col_values_internal;
                (values.get_key(pointer).clone(), values.get(pointer))
            };
            if !keep(&element) {
                self.data[unpack_low(index) as usize] &= !unpack_high(index);
            }
        }
    }

    /// The elements as a `HashSet`. Unlike iteration this reads the blocks
    /// directly, highest element index first.
    pub fn to_plain_set(&self) -> JHashSet<E>
    where
        E: JavaHash + Hash + Eq,
    {
        let mut set = JHashSet::new();
        self.for_each_plain(|element| {
            set.insert(element.clone());
        });
        set
    }

    fn for_each_plain(&self, mut visit: impl FnMut(&E)) {
        let state = self.factory.0.borrow();
        let values = &state.col_values_internal;

        let size = (self.data.len() * 32).min(values.size());
        for i in (0..size).rev() {
            let index = values.get(i);
            if self.data[unpack_low(index) as usize] & unpack_high(index) != 0 {
                visit(values.get_key(i));
            }
        }
    }
}

/// `getCopy()`: a set of the same factory with the same elements.
impl<E> Clone for FastSparseSet<E> {
    fn clone(&self) -> Self {
        Self {
            factory: self.factory.clone(),
            data: self.data.clone(),
            next: self.next.clone(),
        }
    }
}

/// Sets are equal when their blocks are, whatever factory numbered them.
impl<E> PartialEq for FastSparseSet<E> {
    fn eq(&self, other: &Self) -> bool {
        let (shortdata, longdata) = if self.data.len() > other.data.len() {
            (&other.data, &self.data)
        } else {
            (&self.data, &other.data)
        };
        let (common, excess) = longdata.split_at(shortdata.len());
        common == shortdata.as_slice() && excess.iter().all(|&block| block == 0)
    }
}

impl<E> Eq for FastSparseSet<E> {}

/// The hash of the plain set: the sum of the element hashes.
impl<E: JavaHash + Clone> JavaHash for FastSparseSet<E> {
    fn java_hash(&self) -> i32 {
        let mut hash = 0i32;
        self.for_each_plain(|element| hash = hash.wrapping_add(element.java_hash()));
        hash
    }
}

/// `toString()`: the plain set, in its `HashSet` order.
impl<E: JavaHash + Hash + Eq + Clone + Display> Display for FastSparseSet<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{}]", self.to_plain_set().iter().format(", "))
    }
}

impl<E: Clone + Debug> Debug for FastSparseSet<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

/// Walks a set in the order its factory numbered the elements.
pub struct FastSparseSetIterator<'a, E> {
    set: &'a FastSparseSet<E>,
    from: usize,
}

impl<E: Clone> Iterator for FastSparseSetIterator<'_, E> {
    type Item = E;

    fn next(&mut self) -> Option<E> {
        let pointer = self.set.get_next_index(self.from)?;
        self.from = pointer + 1;
        let state = self.set.factory.0.borrow();
        Some(state.col_values_internal.get_key(pointer).clone())
    }
}

impl<'a, E: Clone> IntoIterator for &'a FastSparseSet<E> {
    type Item = E;
    type IntoIter = FastSparseSetIterator<'a, E>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
