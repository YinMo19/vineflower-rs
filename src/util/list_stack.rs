//! `util.collections.ListStack`: the stack operations upstream adds to
//! `ArrayList`, as an extension of `Vec`.
//!
//! `push`, `clone` and the ordinary list operations are `Vec`'s own. `pop()`
//! is `Vec::pop`, which reports an empty stack as `None` where upstream throws.

pub trait ListStack<T> {
    /// The top of the stack.
    fn peek(&self) -> &T;

    /// `pop(count)`: removes `count` elements and returns the last one removed,
    /// the deepest of them; `None` if `count` is not positive.
    fn pop_count(&mut self, count: i32) -> Option<T>;

    fn remove_multiple(&mut self, count: i32);

    /// The element `offset` positions from the end; `-1` is the top.
    fn get_by_offset(&self, offset: i32) -> &T;

    /// Inserts before the element `offset` positions from the end; `0` pushes.
    fn insert_by_offset(&mut self, offset: i32, item: T);
}

impl<T> ListStack<T> for Vec<T> {
    fn peek(&self) -> &T {
        self.get_by_offset(-1)
    }

    fn pop_count(&mut self, count: i32) -> Option<T> {
        let mut popped = None;
        for _ in 0..count {
            popped = Some(self.pop().unwrap());
        }
        popped
    }

    fn remove_multiple(&mut self, count: i32) {
        self.pop_count(count);
    }

    fn get_by_offset(&self, offset: i32) -> &T {
        &self[index_from_end(self.len(), offset)]
    }

    fn insert_by_offset(&mut self, offset: i32, item: T) {
        self.insert(index_from_end(self.len(), offset), item);
    }
}

/// `size() + offset`. A negative sum wraps to an index no list has, so using
/// it fails as it does upstream.
fn index_from_end(len: usize, offset: i32) -> usize {
    len.wrapping_add_signed(offset as isize)
}
