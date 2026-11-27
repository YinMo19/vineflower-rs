// SPDX-License-Identifier: Apache-2.0

use std::marker::PhantomData;
use std::ops::{Index, IndexMut};
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

use index_vec::Idx;
use rustc_hash::FxHashMap;

const SLOTS: usize = u64::BITS as usize;

/// Each allocator owns whole pages, so their handles survive being moved to
/// another arena in the same session. Within a page, the set bits identify
/// the slots packed into its value vector, in order.
pub struct Arena<I, T> {
    // The coordinator indexes all pages from zero. Workers index their current
    // run here and move older, non-adjacent runs into the sparse table.
    pages: Vec<Page<T>>,
    first_page: usize,
    reserved_end: usize,
    page_numbers: Option<Arc<AtomicUsize>>,
    worker_pages: Option<FxHashMap<usize, Page<T>>>,
    next: u64,
    allocations: u64,
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
            first_page: 0,
            reserved_end: 0,
            page_numbers: None,
            worker_pages: None,
            next: 0,
            allocations: 0,
            index: PhantomData,
        }
    }
}

impl<I: Idx, T> Arena<I, T> {
    #[inline]
    pub fn push(&mut self, value: T) -> I {
        let slot = self.next as usize % SLOTS;
        if slot == 0 {
            self.start_page();
        }
        let id = I::from_usize(self.next as usize);
        let page = self.page_mut(self.next as usize / SLOTS);
        page.values.push(value);
        page.present |= 1 << slot;
        self.next += 1;
        self.allocations += 1;
        id
    }

    #[cold]
    fn start_page(&mut self) {
        let number = if let Some(older) = &mut self.worker_pages {
            let following = self.first_page + self.pages.len();
            if following < self.reserved_end {
                following
            } else {
                // Reserve 1, 2, 4, then 8 pages. A one-page arena leaves no
                // unused page numbers and a larger one leaves at most seven.
                let count = (1 + self.allocations as usize / SLOTS)
                    .next_power_of_two()
                    .min(8);
                let first = self
                    .page_numbers
                    .as_ref()
                    .unwrap()
                    .fetch_add(count, Ordering::Relaxed);
                self.reserved_end = first + count;
                if first != following {
                    older.extend((self.first_page..).zip(self.pages.drain(..)));
                    self.first_page = first;
                }
                first
            }
        } else {
            self.page_numbers.as_ref().map_or_else(
                || self.pages.len(),
                |numbers| numbers.fetch_add(1, Ordering::Relaxed),
            )
        };
        let first_slot = number
            .checked_mul(SLOTS)
            .expect("IR handle space exhausted");
        I::from_usize(first_slot);
        if self.worker_pages.is_none() {
            self.pages.resize_with(number, Page::empty);
        }
        self.pages.push(Page::empty());
        self.next = first_slot as u64;
    }

    pub(super) fn fork(&mut self) -> Self {
        assert!(
            self.worker_pages.is_none(),
            "IR workers can only be forked from the coordinator"
        );
        let page_numbers = self
            .page_numbers
            .get_or_insert_with(|| Arc::new(AtomicUsize::new(self.pages.len())));
        Self {
            page_numbers: Some(Arc::clone(page_numbers)),
            worker_pages: Some(FxHashMap::default()),
            ..Self::default()
        }
    }

    pub(super) fn adopt(&mut self, worker: Self) {
        assert!(
            self.worker_pages.is_none(),
            "only the IR coordinator can adopt worker pages"
        );
        let worker_pages = worker
            .worker_pages
            .expect("adoption requires IR worker pages");
        assert!(
            matches!((&self.page_numbers, &worker.page_numbers), (Some(own), Some(other)) if Arc::ptr_eq(own, other)),
            "cannot adopt IR from another session"
        );
        // Leave room for pages still held by other workers.
        let end = worker.next.div_ceil(SLOTS as u64) as usize;
        if end > self.pages.len() {
            self.pages.resize_with(end, Page::empty);
        }
        for (number, page) in worker_pages {
            self.pages[number] = page;
        }
        for (number, page) in (worker.first_page..).zip(worker.pages) {
            self.pages[number] = page;
        }
        self.allocations += worker.allocations;
    }

    pub(super) fn allocated_bytes(&self) -> u64 {
        self.allocations * size_of::<T>() as u64
    }

    /// Release backing storage as well as the contents of dead slots.
    pub(super) fn sweep(&mut self, marks: &Marks) -> u64 {
        assert!(
            self.worker_pages.is_none(),
            "IR worker pages must be adopted before sweeping"
        );
        let live: usize = self
            .pages
            .iter_mut()
            .enumerate()
            .map(|(number, page)| page.sweep(marks.page(number)))
            .sum();
        live as u64 * size_of::<T>() as u64
    }

    #[inline(always)]
    fn page(&self, number: usize) -> &Page<T> {
        self.pages
            .get(number.wrapping_sub(self.first_page))
            .unwrap_or_else(|| self.sparse_page(number))
    }

    #[inline(always)]
    fn page_mut(&mut self, number: usize) -> &mut Page<T> {
        if let Some(page) = self.pages.get_mut(number.wrapping_sub(self.first_page)) {
            return page;
        }
        Self::sparse_page_mut(&mut self.worker_pages, number)
    }

    #[cold]
    fn sparse_page(&self, number: usize) -> &Page<T> {
        &self.worker_pages.as_ref().expect("missing IR page")[&number]
    }

    #[cold]
    fn sparse_page_mut(
        worker_pages: &mut Option<FxHashMap<usize, Page<T>>>,
        number: usize,
    ) -> &mut Page<T> {
        worker_pages
            .as_mut()
            .and_then(|pages| pages.get_mut(&number))
            .expect("missing IR page")
    }
}

impl<T> Page<T> {
    fn empty() -> Self {
        Self {
            present: 0,
            values: Vec::new(),
        }
    }

    fn offset(&self, id: usize) -> usize {
        let bit = 1 << (id % SLOTS);
        assert_ne!(self.present & bit, 0, "released IR handle {id}");
        (self.present & (bit - 1)).count_ones() as usize
    }

    fn sweep(&mut self, keep: u64) -> usize {
        if self.present != keep {
            let mut slots = self.present;
            self.values.retain(|_| {
                let bit = slots & slots.wrapping_neg();
                slots ^= bit;
                keep & bit != 0
            });
            self.values.shrink_to_fit();
            self.present = keep;
        }
        self.values.len()
    }
}

impl<I: Idx, T> Index<I> for Arena<I, T> {
    type Output = T;

    fn index(&self, id: I) -> &T {
        let id = id.index();
        let page = self.page(id / SLOTS);
        &page.values[page.offset(id)]
    }
}

impl<I: Idx, T> IndexMut<I> for Arena<I, T> {
    fn index_mut(&mut self, id: I) -> &mut T {
        let id = id.index();
        let page = self.page_mut(id / SLOTS);
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
