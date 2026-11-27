use std::cmp::Ordering;
use std::iter;

use itertools::Either;
use rustc_hash::FxHashMap;

use super::{Entries, JavaHash};

const UNTREEIFY_THRESHOLD: usize = 6;

#[derive(Clone, Debug)]
pub(super) enum Bucket {
    List(Vec<usize>),
    Tree(Box<TreeBin>),
}

impl Default for Bucket {
    fn default() -> Self {
        Self::List(Vec::new())
    }
}

impl Bucket {
    pub(super) fn indices(&self) -> impl Iterator<Item = usize> + '_ {
        match self {
            Self::List(chain) => Either::Left(chain.iter().copied()),
            Self::Tree(tree) => Either::Right(tree.indices()),
        }
    }

    pub(super) fn remove(&mut self, index: usize, movable: bool) {
        match self {
            Self::List(chain) => {
                let position = chain.iter().position(|&id| id == index).unwrap();
                chain.remove(position);
            }
            Self::Tree(tree) => {
                if !tree.remove(index, movable) {
                    *self = Self::List(tree.indices().collect());
                }
            }
        }
    }

    pub(super) fn replace_index(&mut self, old: usize, new: usize) {
        match self {
            Self::List(chain) => {
                *chain.iter_mut().find(|id| **id == old).unwrap() = new;
            }
            Self::Tree(tree) => tree.replace_index(old, new),
        }
    }

    pub(super) fn split<K: JavaHash, V>(self, bit: usize, entries: &Entries<K, V>) -> (Self, Self) {
        let stays_low = |id| {
            let (_, entry) = entries.get_index(id).unwrap();
            entry.hash as usize & bit == 0
        };
        match self {
            Self::List(chain) if chain.len() <= 1 => {
                if chain.first().is_some_and(|&id| !stays_low(id)) {
                    (Self::default(), Self::List(chain))
                } else {
                    (Self::List(chain), Self::default())
                }
            }
            Self::List(mut low) => {
                let mut high = Vec::new();
                low.retain(|&id| {
                    let low = stays_low(id);
                    if !low {
                        high.push(id);
                    }
                    low
                });
                (Self::List(low), Self::List(high))
            }
            Self::Tree(tree) => {
                // resize() moves a single node directly, including one left
                // behind by iterator removal from a tree bin.
                let both_halves = |chain: Vec<_>| {
                    if chain.len() <= UNTREEIFY_THRESHOLD {
                        Self::List(chain)
                    } else {
                        TreeBin::from_chain(chain, entries)
                    }
                };
                let head = tree.head.unwrap();
                if tree.next(head).is_none() {
                    return if stays_low(head) {
                        (Self::Tree(tree), Self::default())
                    } else {
                        (Self::default(), Self::Tree(tree))
                    };
                }
                let (low, high): (Vec<_>, Vec<_>) = tree.indices().partition(|&id| stays_low(id));
                match (low.is_empty(), high.is_empty()) {
                    (false, false) => (both_halves(low), both_halves(high)),
                    (false, true) if low.len() > UNTREEIFY_THRESHOLD => {
                        (Self::Tree(tree), Self::default())
                    }
                    (true, false) if high.len() > UNTREEIFY_THRESHOLD => {
                        (Self::default(), Self::Tree(tree))
                    }
                    _ => (Self::List(low), Self::List(high)),
                }
            }
        }
    }
}

type Link = Option<usize>;

#[derive(Clone, Copy)]
enum Side {
    Left,
    Right,
}

impl Side {
    fn opposite(self) -> Self {
        match self {
            Self::Left => Self::Right,
            Self::Right => Self::Left,
        }
    }
}

#[derive(Clone, Copy, Debug, Default)]
struct Links {
    prev: Link,
    next: Link,
    parent: Link,
    children: [Link; 2],
    red: bool,
}

/// The red-black tree controls where a newly inserted node goes. Iteration
/// follows the independent linked chain and can begin at a non-root node.
#[derive(Clone, Debug, Default)]
pub(super) struct TreeBin {
    links: FxHashMap<usize, Links>,
    head: Link,
    root: Link,
}

impl TreeBin {
    pub(super) fn head(&self) -> Link {
        self.head
    }

    pub(super) fn next(&self, index: usize) -> Link {
        self.links[&index].next
    }

    fn indices(&self) -> impl Iterator<Item = usize> + '_ {
        iter::successors(self.head, |&id| self.next(id))
    }

    pub(super) fn from_chain<K: JavaHash, V>(chain: Vec<usize>, entries: &Entries<K, V>) -> Bucket {
        let mut tree = Self {
            head: chain.first().copied(),
            ..Self::default()
        };
        tree.links.reserve(chain.len());
        let mut prev = None;
        let mut chain = chain.into_iter().peekable();
        while let Some(id) = chain.next() {
            let (parent, side) = tree.insertion_point(id, entries);
            tree.links.insert(
                id,
                Links {
                    prev,
                    next: chain.peek().copied(),
                    parent,
                    ..Links::default()
                },
            );
            tree.attach(id, parent, side);
            prev = Some(id);
        }
        tree.move_root_to_front();
        Bucket::Tree(Box::new(tree))
    }

    pub(super) fn insert<K: JavaHash, V>(&mut self, id: usize, entries: &Entries<K, V>) {
        let (parent, side) = self.insertion_point(id, entries);
        let parent = parent.unwrap();
        let next = self.next(parent);
        self.links.insert(
            id,
            Links {
                prev: Some(parent),
                next,
                parent: Some(parent),
                ..Links::default()
            },
        );
        self.node(parent).next = Some(id);
        if let Some(next) = next {
            self.node(next).prev = Some(id);
        }

        self.attach(id, Some(parent), side);
        self.move_root_to_front();
    }

    fn insertion_point<K: JavaHash, V>(&self, id: usize, entries: &Entries<K, V>) -> (Link, Side) {
        let (key, entry) = entries.get_index(id).unwrap();
        let mut current = self.root;
        let mut parent = None;
        let mut side = Side::Left;
        while let Some(id) = current {
            let (other_key, other) = entries.get_index(id).unwrap();
            let order = entry
                .hash
                .cmp(&other.hash)
                .then_with(|| compare_keys(key, entry.serial, other_key, other.serial));
            side = if order == Ordering::Greater {
                Side::Right
            } else {
                Side::Left
            };
            parent = current;
            current = self.child(id, side);
        }
        (parent, side)
    }

    fn attach(&mut self, id: usize, parent: Link, side: Side) {
        if let Some(parent) = parent {
            self.set_child(parent, side, Some(id));
            self.balance_insertion(id);
        } else {
            self.root = Some(id);
        }
    }

    fn move_root_to_front(&mut self) {
        let root = self.root.unwrap();
        if self.head == Some(root) {
            return;
        }
        self.unlink_chain(root);
        let head = self.head.unwrap();
        self.node(head).prev = Some(root);
        let node = self.node(root);
        node.prev = None;
        node.next = Some(head);
        self.head = Some(root);
    }

    fn unlink_chain(&mut self, id: usize) {
        let Links { prev, next, .. } = self.links[&id];
        if let Some(prev) = prev {
            self.node(prev).next = next;
        } else {
            self.head = next;
        }
        if let Some(next) = next {
            self.node(next).prev = prev;
        }
    }

    /// Returns whether the bin remains a tree. When removing via an iterator,
    /// JDK keeps the tree even when small and never moves its root to the head.
    fn remove(&mut self, id: usize, movable: bool) -> bool {
        self.unlink_chain(id);
        if self.head.is_none() {
            return false;
        }
        let root = self.root.unwrap();
        if movable
            && (self.child(root, Side::Right).is_none()
                || self
                    .child(root, Side::Left)
                    .and_then(|left| self.child(left, Side::Left))
                    .is_none())
        {
            return false;
        }

        let [left, right] = self.links[&id].children;
        let replacement = match (left, right) {
            (Some(left), Some(right)) => self.move_to_successor(id, left, right).unwrap_or(id),
            _ => left.or(right).unwrap_or(id),
        };
        if replacement != id {
            self.replace_child(id, Some(replacement));
            if self.root == Some(replacement) {
                self.node(replacement).red = false;
            }
        }
        if !self.links[&id].red {
            self.balance_deletion(replacement);
        }
        if replacement == id {
            self.replace_child(id, None);
        }
        self.links.remove(&id);
        if movable {
            self.move_root_to_front();
        }
        true
    }

    /// Swap only tree positions with the inorder successor. Moving payloads
    /// would change the independent iteration sequence.
    fn move_to_successor(&mut self, id: usize, left: usize, right: usize) -> Link {
        let mut successor = right;
        while let Some(next) = self.child(successor, Side::Left) {
            successor = next;
        }
        let successor_links = self.links[&successor];
        self.node(successor).red = self.links[&id].red;
        self.node(id).red = successor_links.red;
        if successor == right {
            self.set_child(successor, Side::Right, Some(id));
            // replace_child below still needs id's original parent.
        } else {
            self.set_child(successor_links.parent.unwrap(), Side::Left, Some(id));
            self.set_child(successor, Side::Right, Some(right));
            self.node(right).parent = Some(successor);
        }
        let right_child = successor_links.children[Side::Right as usize];
        self.set_child(id, Side::Left, None);
        self.set_child(id, Side::Right, right_child);
        if let Some(right_child) = right_child {
            self.node(right_child).parent = Some(id);
        }
        self.set_child(successor, Side::Left, Some(left));
        self.node(left).parent = Some(successor);
        self.replace_child(id, Some(successor));
        self.node(id).parent = if successor == right {
            Some(successor)
        } else {
            successor_links.parent
        };
        right_child
    }

    /// The owning entry arena may move its last entry into a vacated index.
    /// Rename that ID in its immediate neighbors, without scanning the bin.
    fn replace_index(&mut self, old: usize, new: usize) {
        let node = self.links.remove(&old).unwrap();
        if let Some(parent) = node.parent {
            let side = self.side_of(parent, old);
            self.set_child(parent, side, Some(new));
        } else {
            self.root = Some(new);
        }
        for child in node.children.into_iter().flatten() {
            self.node(child).parent = Some(new);
        }
        if let Some(prev) = node.prev {
            self.node(prev).next = Some(new);
        } else {
            self.head = Some(new);
        }
        if let Some(next) = node.next {
            self.node(next).prev = Some(new);
        }
        self.links.insert(new, node);
    }

    fn node(&mut self, id: usize) -> &mut Links {
        self.links.get_mut(&id).unwrap()
    }

    fn child(&self, id: usize, side: Side) -> Link {
        self.links[&id].children[side as usize]
    }

    fn set_child(&mut self, id: usize, side: Side, child: Link) {
        self.node(id).children[side as usize] = child;
    }

    fn side_of(&self, parent: usize, child: usize) -> Side {
        if self.child(parent, Side::Left) == Some(child) {
            Side::Left
        } else {
            debug_assert_eq!(self.child(parent, Side::Right), Some(child));
            Side::Right
        }
    }

    fn is_red(&self, id: Link) -> bool {
        id.is_some_and(|id| self.links[&id].red)
    }

    fn replace_child(&mut self, id: usize, child: Link) {
        let parent = self.links[&id].parent;
        if let Some(parent) = parent {
            self.set_child(parent, self.side_of(parent, id), child);
        } else {
            self.root = child;
        }
        if let Some(child) = child {
            self.node(child).parent = parent;
        }
    }

    /// A left rotation takes its pivot from the right, and vice versa.
    fn rotate(&mut self, id: usize, direction: Side) {
        let pivot_side = direction.opposite();
        let pivot = self.child(id, pivot_side).unwrap();
        let inner = self.child(pivot, direction);
        self.set_child(id, pivot_side, inner);
        if let Some(inner) = inner {
            self.node(inner).parent = Some(id);
        }
        self.replace_child(id, Some(pivot));
        if self.root == Some(pivot) {
            self.node(pivot).red = false;
        }
        self.set_child(pivot, direction, Some(id));
        self.node(id).parent = Some(pivot);
    }

    fn balance_insertion(&mut self, mut id: usize) {
        self.node(id).red = true;
        loop {
            let Some(parent) = self.links[&id].parent else {
                self.node(id).red = false;
                return;
            };
            let Some(grandparent) = self.links[&parent].parent else {
                return;
            };
            if !self.links[&parent].red {
                return;
            }
            let side = self.side_of(grandparent, parent);
            let uncle = self.child(grandparent, side.opposite());
            if let Some(uncle) = uncle.filter(|&uncle| self.links[&uncle].red) {
                self.node(uncle).red = false;
                self.node(parent).red = false;
                self.node(grandparent).red = true;
                id = grandparent;
            } else {
                let new_parent = if self.child(parent, side.opposite()) == Some(id) {
                    self.rotate(parent, side);
                    id
                } else {
                    parent
                };
                self.node(new_parent).red = false;
                self.node(grandparent).red = true;
                self.rotate(grandparent, side.opposite());
                return;
            }
        }
    }

    fn balance_deletion(&mut self, mut id: usize) {
        while self.root != Some(id) {
            let Some(parent) = self.links[&id].parent else {
                self.node(id).red = false;
                self.root = Some(id);
                return;
            };
            if self.links[&id].red {
                self.node(id).red = false;
                return;
            }
            let side = self.side_of(parent, id);
            let other = side.opposite();
            if let Some(sibling) = self
                .child(parent, other)
                .filter(|&sibling| self.links[&sibling].red)
            {
                self.node(sibling).red = false;
                self.node(parent).red = true;
                self.rotate(parent, side);
            }
            let Some(mut sibling) = self.child(parent, other) else {
                id = parent;
                continue;
            };
            let near = self.child(sibling, side);
            let far = self.child(sibling, other);
            if !self.is_red(far) && !self.is_red(near) {
                self.node(sibling).red = true;
                id = parent;
                continue;
            }
            if !self.is_red(far) {
                if let Some(near) = near {
                    self.node(near).red = false;
                }
                self.node(sibling).red = true;
                self.rotate(sibling, other);
                sibling = self.child(parent, other).unwrap();
            }
            self.node(sibling).red = self.links[&parent].red;
            if let Some(far) = self.child(sibling, other) {
                self.node(far).red = false;
            }
            self.node(parent).red = false;
            self.rotate(parent, side);
            return;
        }
    }
}

fn compare_keys<K: JavaHash>(key: &K, serial: u32, other: &K, other_serial: u32) -> Ordering {
    if let Some(order) = key
        .java_cmp(other)
        .filter(|&order| order != Ordering::Equal)
    {
        return order;
    }
    match (key.java_class_name(), other.java_class_name()) {
        (Some(name), Some(other_name)) => name
            .encode_utf16()
            .cmp(other_name.encode_utf16())
            .then_with(|| {
                let identity = key.java_identity().unwrap_or_else(|| u64::from(serial));
                let other = other
                    .java_identity()
                    .unwrap_or_else(|| u64::from(other_serial));
                if identity <= other {
                    Ordering::Less
                } else {
                    Ordering::Greater
                }
            }),
        (None, Some(_)) => Ordering::Less,
        (Some(_), None) => Ordering::Greater,
        (None, None) => Ordering::Less,
    }
}
