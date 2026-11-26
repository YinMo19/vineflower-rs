// SPDX-License-Identifier: Apache-2.0

use std::marker::PhantomData;
use std::ops::{Index, IndexMut};

use index_vec::Idx;

const SLOTS: usize = u64::BITS as usize;

/// Handles increase in allocation order for the entire run. Within each page
/// the set bits identify the slots packed into its value vector, in order.
pub struct Arena<I, T> {
    pages: Vec<Page<T>>,
    next: usize,
    index: PhantomData<I>,
}

struct Page<T> {
    present: u64,
    values: Vec<T>,
}

impl<I, T> Default for Arena<I, T> {
    fn default() -> Self {
        Self {
            pages: Vec::new(),
            next: 0,
            index: PhantomData,
        }
    }
}

impl<I: Idx, T> Arena<I, T> {
    pub fn push(&mut self, value: T) -> I {
        let id = I::from_usize(self.next);
        let offset = self.next % SLOTS;
        if offset == 0 {
            self.pages.push(Page {
                present: 0,
                values: Vec::new(),
            });
        }
        let page = self.pages.last_mut().unwrap();
        page.values.push(value);
        page.present |= 1 << offset;
        self.next += 1;
        id
    }

    pub(super) fn allocated_bytes(&self) -> u64 {
        self.next as u64 * size_of::<T>() as u64
    }

    /// Release backing storage as well as the contents of dead slots.
    pub(super) fn sweep(&mut self, marks: &Marks) -> u64 {
        let mut live = 0;
        for (i, page) in self.pages.iter_mut().enumerate() {
            let keep = marks.page(i);
            if page.present != keep {
                let mut slots = page.present;
                page.values.retain(|_| {
                    let bit = slots & slots.wrapping_neg();
                    slots ^= bit;
                    keep & bit != 0
                });
                page.values.shrink_to_fit();
                page.present = keep;
            }
            live += page.values.len();
        }
        live as u64 * size_of::<T>() as u64
    }
}

impl<T> Page<T> {
    fn offset(&self, id: usize) -> usize {
        let bit = 1 << (id % SLOTS);
        assert_ne!(self.present & bit, 0, "released IR handle {id}");
        (self.present & (bit - 1)).count_ones() as usize
    }
}

impl<I: Idx, T> Index<I> for Arena<I, T> {
    type Output = T;

    fn index(&self, id: I) -> &T {
        let id = id.index();
        let page = &self.pages[id / SLOTS];
        &page.values[page.offset(id)]
    }
}

impl<I: Idx, T> IndexMut<I> for Arena<I, T> {
    fn index_mut(&mut self, id: I) -> &mut T {
        let id = id.index();
        let page = &mut self.pages[id / SLOTS];
        let offset = page.offset(id);
        &mut page.values[offset]
    }
}

#[derive(Default)]
pub(super) struct Marks(Vec<u64>);

impl Marks {
    pub(super) fn insert(&mut self, id: impl Idx) -> bool {
        let id = id.index();
        let page = id / SLOTS;
        if page >= self.0.len() {
            self.0.resize(page + 1, 0);
        }
        let bit = 1 << (id % SLOTS);
        let previous = self.0[page];
        self.0[page] |= bit;
        previous & bit == 0
    }

    pub(super) fn contains(&self, id: impl Idx) -> bool {
        let id = id.index();
        self.page(id / SLOTS) & (1 << (id % SLOTS)) != 0
    }

    fn page(&self, page: usize) -> u64 {
        self.0.get(page).copied().unwrap_or(0)
    }
}
