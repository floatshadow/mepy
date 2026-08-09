//! A persistent vector backed by a relaxed radix balanced tree.
//!
//! [`RrbVec`] uses 32-way nodes and shares unchanged nodes between versions.
//! Regular branches use direct radix indexing. Relaxed branches use cumulative
//! subtree sizes and a short forward scan. Concatenation and slicing copy only
//! tree edges and boundary leaves.
//!
//! The balancing rules follow Bagwell and Rompf's
//! [RRB-tree paper](https://infoscience.epfl.ch/server/api/core/bitstreams/e5d662ea-1e8d-4dda-b917-8cbb8bb40bf9/content).

mod balance;
mod builder;
mod concat;
mod iter;
mod node;

use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::{Bound, Index, RangeBounds};
use std::sync::Arc;

use builder::Built;
use concat::{append_leaf, concat_roots};
pub use iter::Iter;
use node::{BRANCH_FACTOR, Node, SharedNode, compact_root, get, normalize_root, split, updated};

/// An immutable vector with efficient concatenation and slicing.
///
/// Cloning an `RrbVec` takes constant time and does not require `T: Clone`.
/// Operations that replace or move values between boundary leaves require
/// `T: Clone`; unchanged tree nodes remain shared.
///
/// # Examples
///
/// ```
/// use plti_adt::rrb::RrbVec;
///
/// let left: RrbVec<_> = (0..40).collect();
/// let right: RrbVec<_> = (40..80).collect();
/// let joined = left.concat(&right);
///
/// assert_eq!(joined.len(), 80);
/// assert_eq!(joined.get(63), Some(&63));
/// assert_eq!(left.len(), 40);
/// ```
pub struct RrbVec<T> {
    len: usize,
    height: u8,
    root: Option<SharedNode<T>>,
    tail: Option<SharedNode<T>>,
    debt: EdgeDebt,
}

#[derive(Clone, Copy, Default)]
struct EdgeDebt {
    left: bool,
    right: bool,
}

impl EdgeDebt {
    const NONE: Self = Self::new(false, false);

    const fn new(left: bool, right: bool) -> Self {
        Self { left, right }
    }
}

impl<T> RrbVec<T> {
    /// Creates an empty vector.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            len: 0,
            height: 0,
            root: None,
            tail: None,
            debt: EdgeDebt::NONE,
        }
    }

    /// Returns the number of values in the vector.
    #[must_use]
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Returns `true` when the vector has no values.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns a reference to the value at `index`.
    ///
    /// This operation takes `O(log_32 n)` time and does not allocate.
    #[must_use]
    pub fn get(&self, index: usize) -> Option<&T> {
        if index >= self.len {
            return None;
        }

        let root_len = self.root_len();
        if index < root_len {
            return self.root.as_ref().map(|root| get(root, self.height, index));
        }
        self.tail
            .as_deref()
            .and_then(|tail| tail.as_leaf().get(index - root_len))
    }

    /// Returns the first value, or `None` when the vector is empty.
    #[must_use]
    pub fn first(&self) -> Option<&T> {
        self.get(0)
    }

    /// Returns the last value, or `None` when the vector is empty.
    #[must_use]
    pub fn last(&self) -> Option<&T> {
        self.len.checked_sub(1).and_then(|index| self.get(index))
    }

    /// Returns an iterator over shared references in sequence order.
    ///
    /// The iterator visits the tree directly and does not flatten it.
    pub fn iter(&self) -> Iter<'_, T> {
        Iter::new(self)
    }

    fn root_len(&self) -> usize {
        self.root.as_ref().map_or(0, |root| root.len)
    }

    fn from_built(built: Built<T>) -> Self {
        Self {
            len: built.len,
            height: built.height,
            root: built.root,
            tail: built.tail,
            debt: EdgeDebt::NONE,
        }
    }

    fn from_parts(
        root: Option<SharedNode<T>>,
        height: u8,
        tail: Option<SharedNode<T>>,
        len: usize,
        debt: EdgeDebt,
    ) -> Self {
        let (root, height) = normalize_root(root, height);
        let tail = tail.filter(|node| node.len > 0);
        debug_assert_eq!(
            root.as_ref().map_or(0, |node| node.len) + tail.as_ref().map_or(0, |node| node.len),
            len
        );
        Self {
            len,
            height,
            root,
            tail,
            debt,
        }
    }
}

impl<T: Clone> RrbVec<T> {
    fn from_parts_compact(
        root: Option<SharedNode<T>>,
        height: u8,
        tail: Option<SharedNode<T>>,
        len: usize,
        debt: EdgeDebt,
    ) -> Self {
        let max_extra_slots =
            node::MAX_EXTRA_SLOTS + usize::from(debt.left) + usize::from(debt.right);
        let (root, height) = compact_root(root, height, max_extra_slots);
        Self::from_parts(root, height, tail, len, debt)
    }

    /// Returns a vector with the value at `index` replaced.
    ///
    /// The selected leaf and its root path are copied. Other nodes stay shared.
    ///
    /// # Panics
    ///
    /// Panics when `index >= self.len()`.
    #[must_use]
    pub fn set(&self, index: usize, value: T) -> Self {
        assert!(
            index < self.len,
            "RRB vector index {index} is out of bounds for length {}",
            self.len
        );

        let root_len = self.root_len();
        if index < root_len {
            let root = self.root.as_ref().expect("the index lies in the root");
            return Self::from_parts(
                Some(updated(root, self.height, index, value)),
                self.height,
                self.tail.clone(),
                self.len,
                self.debt,
            );
        }

        let mut tail = self
            .tail
            .as_deref()
            .expect("the index lies in the tail")
            .as_leaf()
            .to_vec();
        tail[index - root_len] = value;
        Self::from_parts(
            self.root.clone(),
            self.height,
            Some(Node::leaf(tail)),
            self.len,
            self.debt,
        )
    }

    /// Returns a vector with `value` appended at the right end.
    ///
    /// Appending into a non-full tail does not visit the tree. A full tail
    /// becomes a shared tree leaf, and one branch on each level of the right
    /// edge is copied.
    #[must_use]
    pub fn push_back(&self, value: T) -> Self {
        let len = self.len.checked_add(1).expect("RRB vector length overflow");
        match self.tail.as_deref().map(Node::as_leaf) {
            None => Self::from_parts(
                self.root.clone(),
                self.height,
                Some(Node::leaf(vec![value])),
                len,
                self.debt,
            ),
            Some(tail) if tail.len() < BRANCH_FACTOR => {
                let mut new_tail = Vec::with_capacity(tail.len() + 1);
                new_tail.extend_from_slice(tail);
                new_tail.push(value);
                Self::from_parts(
                    self.root.clone(),
                    self.height,
                    Some(Node::leaf(new_tail)),
                    len,
                    self.debt,
                )
            }
            Some(_) => {
                let leaf = Arc::clone(self.tail.as_ref().expect("the full tail is present"));
                let (root, height) = append_leaf(self.root.clone(), self.height, leaf);
                Self::from_parts(
                    root,
                    height,
                    Some(Node::leaf(vec![value])),
                    len,
                    EdgeDebt::new(self.debt.left, false),
                )
            }
        }
    }

    /// Concatenates two vectors while sharing nodes outside the touching edges.
    ///
    /// The merge takes `O(log_32 n)` time for fixed 32-way nodes. At most a
    /// constant-size group is redistributed at each tree level.
    #[must_use]
    pub fn concat(&self, other: &Self) -> Self {
        if self.is_empty() {
            return other.clone();
        }
        if other.is_empty() {
            return self.clone();
        }

        let len = self
            .len
            .checked_add(other.len)
            .expect("RRB vector length overflow");

        if len <= BRANCH_FACTOR {
            return self.iter().chain(other).cloned().collect();
        }

        if other.root.is_none() {
            return self.concat_tail_only(other, len);
        }

        let (left_root, left_height) = self.full_root();
        let right_root = Arc::clone(other.root.as_ref().expect("checked above"));
        let (root, height) = concat_roots(left_root, left_height, right_root, other.height);
        Self::from_parts_compact(
            Some(root),
            height,
            other.tail.clone(),
            len,
            EdgeDebt::new(self.debt.left, other.debt.right),
        )
    }

    /// Splits the vector before `index`.
    ///
    /// The first result contains `0..index`; the second contains
    /// `index..self.len()`.
    ///
    /// # Panics
    ///
    /// Panics when `index > self.len()`.
    #[must_use]
    pub fn split_at(&self, index: usize) -> (Self, Self) {
        assert!(
            index <= self.len,
            "RRB vector split index {index} is out of bounds for length {}",
            self.len
        );
        if index == 0 {
            return (Self::new(), self.clone());
        }
        if index == self.len {
            return (self.clone(), Self::new());
        }

        let root_len = self.root_len();
        if index >= root_len {
            let cut = index - root_len;
            let tail = self.tail.as_deref().map_or(&[][..], Node::as_leaf);
            let left_tail = cloned_slice(&tail[..cut]);
            let right_tail = cloned_slice(&tail[cut..]);
            return (
                Self::from_parts_compact(
                    self.root.clone(),
                    self.height,
                    left_tail,
                    index,
                    self.debt,
                ),
                Self::from_parts_compact(None, 0, right_tail, self.len - index, EdgeDebt::NONE),
            );
        }

        let root = self.root.as_ref().expect("the split lies in the root");
        let (left_root, right_root) = split(root, self.height, index);
        (
            Self::from_parts_compact(
                left_root,
                self.height,
                None,
                index,
                EdgeDebt::new(self.debt.left, true),
            ),
            Self::from_parts_compact(
                right_root,
                self.height,
                self.tail.clone(),
                self.len - index,
                EdgeDebt::new(true, self.debt.right),
            ),
        )
    }

    /// Returns the values selected by `range`.
    ///
    /// The range uses the same inclusive, exclusive, and unbounded forms as a
    /// standard slice range.
    ///
    /// # Panics
    ///
    /// Panics when the range is reversed or outside the vector.
    #[must_use]
    pub fn slice<R>(&self, range: R) -> Self
    where
        R: RangeBounds<usize>,
    {
        let (start, end) = range_limits(range, self.len);
        let (_, suffix) = self.split_at(start);
        suffix.split_at(end - start).0
    }

    /// Returns a vector with `value` inserted before `index`.
    ///
    /// `index == self.len()` appends the value.
    ///
    /// # Panics
    ///
    /// Panics when `index > self.len()`.
    #[must_use]
    pub fn insert(&self, index: usize, value: T) -> Self {
        assert!(
            index <= self.len,
            "RRB vector insertion index {index} is out of bounds for length {}",
            self.len
        );
        if index == self.len {
            return self.push_back(value);
        }
        let (left, right) = self.split_at(index);
        left.push_back(value).concat(&right)
    }

    fn full_root(&self) -> (SharedNode<T>, u8) {
        match (&self.root, &self.tail) {
            (Some(root), None) => (Arc::clone(root), self.height),
            (None, Some(tail)) => (Arc::clone(tail), 0),
            (Some(root), Some(tail)) => {
                let (root, height) =
                    append_leaf(Some(Arc::clone(root)), self.height, Arc::clone(tail));
                (root.expect("appending a leaf produces a root"), height)
            }
            (None, None) => panic!("an empty vector has no full root"),
        }
    }

    fn concat_tail_only(&self, other: &Self, len: usize) -> Self {
        let right_tail = other
            .tail
            .as_deref()
            .expect("a non-empty tail-only vector")
            .as_leaf();
        let Some(left_tail) = self.tail.as_deref().map(Node::as_leaf) else {
            return Self::from_parts(
                self.root.clone(),
                self.height,
                other.tail.clone(),
                len,
                EdgeDebt::new(self.debt.left, self.debt.right),
            );
        };

        let combined_len = left_tail.len() + right_tail.len();
        let mut values = Vec::with_capacity(combined_len);
        values.extend_from_slice(left_tail);
        values.extend_from_slice(right_tail);

        if combined_len <= BRANCH_FACTOR {
            return Self::from_parts(
                self.root.clone(),
                self.height,
                Some(Node::leaf(values)),
                len,
                EdgeDebt::new(self.debt.left, self.debt.right),
            );
        }

        let tail = values.split_off(BRANCH_FACTOR);
        let leaf = Node::leaf(values);
        let (root, height) = append_leaf(self.root.clone(), self.height, leaf);
        Self::from_parts(
            root,
            height,
            Some(Node::leaf(tail)),
            len,
            EdgeDebt::new(self.debt.left, other.debt.right),
        )
    }

    #[cfg(test)]
    fn assert_valid(&self) {
        let root_len = self
            .root
            .as_ref()
            .map_or(0, |root| node::assert_valid(root, self.height, true));
        if let Some(root) = &self.root {
            node::assert_extra_slots(root, true, true, self.debt.left, self.debt.right);
        }
        let tail_len = self.tail.as_ref().map_or(0, |tail| {
            assert!(matches!(tail.kind, node::NodeKind::Leaf(_)));
            assert!((1..=BRANCH_FACTOR).contains(&tail.len));
            tail.len
        });
        assert_eq!(root_len + tail_len, self.len);
        assert_eq!(self.root.is_none(), root_len == 0);
        assert_eq!(self.tail.is_none(), tail_len == 0);
    }
}

fn cloned_slice<T: Clone>(values: &[T]) -> Option<SharedNode<T>> {
    (!values.is_empty()).then(|| Node::leaf(values.to_vec()))
}

fn range_limits<R: RangeBounds<usize>>(range: R, len: usize) -> (usize, usize) {
    let start = match range.start_bound() {
        Bound::Included(&index) => index,
        Bound::Excluded(&index) => index
            .checked_add(1)
            .expect("RRB vector range start overflow"),
        Bound::Unbounded => 0,
    };
    let end = match range.end_bound() {
        Bound::Included(&index) => index.checked_add(1).expect("RRB vector range end overflow"),
        Bound::Excluded(&index) => index,
        Bound::Unbounded => len,
    };
    assert!(
        start <= end,
        "RRB vector range starts at {start} but ends at {end}"
    );
    assert!(
        end <= len,
        "RRB vector range end {end} is out of bounds for length {len}"
    );
    (start, end)
}

impl<T> Clone for RrbVec<T> {
    fn clone(&self) -> Self {
        Self {
            len: self.len,
            height: self.height,
            root: self.root.clone(),
            tail: self.tail.clone(),
            debt: self.debt,
        }
    }
}

impl<T> Default for RrbVec<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> From<Vec<T>> for RrbVec<T> {
    fn from(values: Vec<T>) -> Self {
        Self::from_built(builder::from_values(values))
    }
}

impl<T> FromIterator<T> for RrbVec<T> {
    fn from_iter<I: IntoIterator<Item = T>>(values: I) -> Self {
        Self::from(values.into_iter().collect::<Vec<_>>())
    }
}

impl<T> Index<usize> for RrbVec<T> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        self.get(index).unwrap_or_else(|| {
            panic!(
                "RRB vector index {index} is out of bounds for length {}",
                self.len
            )
        })
    }
}

impl<'a, T> IntoIterator for &'a RrbVec<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<T: fmt::Debug> fmt::Debug for RrbVec<T> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.debug_list().entries(self).finish()
    }
}

impl<T: PartialEq> PartialEq for RrbVec<T> {
    fn eq(&self, other: &Self) -> bool {
        self.len == other.len && self.iter().eq(other)
    }
}

impl<T: Eq> Eq for RrbVec<T> {}

impl<T: Hash> Hash for RrbVec<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.len.hash(state);
        for value in self {
            value.hash(state);
        }
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;
    use std::sync::atomic::{AtomicUsize, Ordering};

    use proptest::collection::vec;
    use proptest::prelude::*;

    use super::node::{contains_ptr, max_extra_slots};
    use super::*;

    #[test]
    fn builds_and_indexes_tree_boundaries() {
        for &len in &[0, 1, 31, 32, 33, 1023, 1024, 1025, 32_767, 32_768, 32_769] {
            let vector: RrbVec<_> = (0..len).collect();
            vector.assert_valid();
            assert_eq!(vector.len(), len);
            assert!(vector.iter().copied().eq(0..len));
            for index in 0..len {
                assert_eq!(vector.get(index), Some(&index));
            }
            assert_eq!(vector.get(len), None);
        }
    }

    #[test]
    fn clone_does_not_require_clone_values() {
        struct NonClone(u8);

        let vector: RrbVec<_> = vec![NonClone(7), NonClone(9)].into();
        let cloned = vector.clone();
        assert_eq!(cloned[0].0, 7);
        assert_eq!(cloned[1].0, 9);
    }

    #[test]
    fn update_shares_untouched_subtrees() {
        let vector: RrbVec<_> = (0..4097).collect();
        let root = vector.root.as_ref().unwrap();
        let shared = Arc::clone(&root.as_branch().children[0]);
        let updated = vector.set(vector.root_len() - 1, usize::MAX);

        vector.assert_valid();
        updated.assert_valid();
        assert!(contains_ptr(updated.root.as_ref().unwrap(), &shared));
        assert_eq!(vector[vector.root_len() - 1], vector.root_len() - 1);
        assert_eq!(updated[vector.root_len() - 1], usize::MAX);
    }

    #[test]
    fn flushing_a_full_tail_shares_its_leaf() {
        let vector: RrbVec<_> = (0..BRANCH_FACTOR).collect();
        let tail = Arc::clone(vector.tail.as_ref().unwrap());

        let appended = vector.push_back(BRANCH_FACTOR);

        assert!(Arc::ptr_eq(appended.root.as_ref().unwrap(), &tail));
        assert_eq!(appended.last(), Some(&BRANCH_FACTOR));
    }

    #[test]
    fn concatenation_clones_only_a_bounded_leaf_window() {
        struct Counted {
            value: usize,
            clones: Arc<AtomicUsize>,
        }

        impl Clone for Counted {
            fn clone(&self) -> Self {
                self.clones.fetch_add(1, Ordering::Relaxed);
                Self {
                    value: self.value,
                    clones: Arc::clone(&self.clones),
                }
            }
        }

        let clones = Arc::new(AtomicUsize::new(0));
        let mut vector = RrbVec::new();
        for chunk_index in 0..300 {
            let chunk: RrbVec<_> = (0..chunk_index % 41 + 1)
                .map(|offset| Counted {
                    value: chunk_index * 100 + offset,
                    clones: Arc::clone(&clones),
                })
                .collect();
            clones.store(0, Ordering::Relaxed);
            vector = chunk.concat(&vector);
            let copied = clones.load(Ordering::Relaxed);
            assert!(
                copied <= 2 * BRANCH_FACTOR * BRANCH_FACTOR + 2 * BRANCH_FACTOR,
                "one concatenation cloned {copied} leaf values"
            );
        }
    }

    #[test]
    fn concat_keeps_the_two_level_extra_slot_bound() {
        let mut vector = RrbVec::new();
        for chunk in 0..300 {
            let values: RrbVec<_> = (0..(chunk % 47 + 1))
                .map(|offset| chunk * 100 + offset)
                .collect();
            vector = vector.concat(&values);
            vector.assert_valid();
        }

        let extra = vector.root.as_ref().map_or(0, max_extra_slots);
        assert!(
            extra <= node::MAX_EXTRA_SLOTS,
            "maximum extra-slot count was {extra}"
        );
    }

    #[test]
    fn split_adds_at_most_one_extra_slot_and_concat_removes_it() {
        fn extra_slots<T>(vector: &RrbVec<T>) -> usize {
            vector.root.as_ref().map_or(0, max_extra_slots)
        }

        let mut vector = RrbVec::new();
        for chunk in 0..240 {
            let values: RrbVec<_> = (0..(chunk % 53 + 1))
                .map(|offset| chunk * 100 + offset)
                .collect();
            vector = vector.concat(&values);
        }

        for index in (0..=vector.len()).step_by(37) {
            let (left, right) = vector.split_at(index);
            left.assert_valid();
            right.assert_valid();
            assert!(extra_slots(&left) <= node::MAX_EXTRA_SLOTS + 1);
            assert!(extra_slots(&right) <= node::MAX_EXTRA_SLOTS + 1);

            let joined = left.concat(&right);
            joined.assert_valid();
            assert!(extra_slots(&joined) <= node::MAX_EXTRA_SLOTS);
            assert!(joined.iter().eq(&vector));
        }
    }

    #[test]
    fn narrow_slice_compacts_height_to_its_own_length() {
        let vector: RrbVec<_> = (0..1_100_000).collect();
        let slice = vector.slice(1_048_575..1_048_577);

        slice.assert_valid();
        assert_eq!(
            slice.iter().copied().collect::<Vec<_>>(),
            [1_048_575, 1_048_576]
        );
        assert_eq!(slice.height, 0);
    }

    #[test]
    fn concat_preserves_only_untouched_outer_debt() {
        let vector: RrbVec<_> = (0..100_000).collect();
        let (_, suffix) = vector.split_at(12_345);
        assert!(suffix.debt.left);
        assert!(suffix.debt.right == vector.debt.right);

        let joined = suffix.concat(&RrbVec::from(vec![100_000, 100_001]));
        joined.assert_valid();
        assert!(joined.debt.left);
        assert!(!joined.debt.right);

        let (left, right) = vector.split_at(45_678);
        let restored = left.concat(&right);
        restored.assert_valid();
        assert!(!restored.debt.left);
        assert!(!restored.debt.right);
    }

    #[test]
    fn tail_only_concat_preserves_untouched_right_debt() {
        let mut vector = RrbVec::new();
        for chunk in 0..600 {
            let values: RrbVec<_> = (0..chunk % 53 + 1)
                .map(|offset| chunk * 100 + offset)
                .collect();
            vector = vector.concat(&values);
        }
        let (left, _) = vector.split_at(736);
        assert!(left.debt.right);
        assert_eq!(
            left.root.as_ref().map_or(0, max_extra_slots),
            node::MAX_EXTRA_SLOTS + 1
        );

        let joined = left.concat(&RrbVec::from(vec![usize::MAX]));

        joined.assert_valid();
        assert!(joined.debt.right);
        assert_eq!(joined.last(), Some(&usize::MAX));
    }

    #[test]
    fn stateful_sparse_versions_preserve_the_extra_slot_bound() {
        fn next(state: &mut u64) -> usize {
            *state ^= *state << 13;
            *state ^= *state >> 7;
            *state ^= *state << 17;
            *state as usize
        }

        fn violation<T>(
            node: &SharedNode<T>,
            height: u8,
            path: &mut Vec<usize>,
        ) -> Option<(Vec<usize>, u8, Vec<usize>)> {
            let node::NodeKind::Branch(branch) = &node.kind else {
                return None;
            };
            let counts: Vec<_> = branch
                .children
                .iter()
                .map(|child| child.entry_count())
                .collect();
            let extra = counts.len() - counts.iter().sum::<usize>().div_ceil(BRANCH_FACTOR);
            if extra > node::MAX_EXTRA_SLOTS {
                return Some((path.clone(), height, counts));
            }
            for (index, child) in branch.children.iter().enumerate() {
                path.push(index);
                if let Some(found) = violation(child, height - 1, path) {
                    return Some(found);
                }
                path.pop();
            }
            None
        }

        fn assert_concat_bound<T>(
            vector: &RrbVec<T>,
            step: usize,
            left_len: usize,
            right_len: usize,
        ) {
            let extra = vector.root.as_ref().map_or(0, max_extra_slots);
            let allowed = node::MAX_EXTRA_SLOTS
                + usize::from(vector.debt.left)
                + usize::from(vector.debt.right);
            let details = vector
                .root
                .as_ref()
                .and_then(|root| violation(root, vector.height, &mut Vec::new()));
            assert!(
                extra <= allowed,
                "step {step}, left {left_len}, right {right_len}, produced local extra-slot count {extra}, allowed {allowed}: {details:?}"
            );
        }

        for seed in [0x91ab_7334_ce91_5f01_u64, 2, 3] {
            let base: RrbVec<i32> = (0..100_000).collect();
            let mut versions = vec![base];
            let mut state = seed;

            for step in 0..20_000 {
                let a = next(&mut state) % versions.len();
                let current = &versions[a];
                let operation = next(&mut state) % 4;

                let next_vector = match operation {
                    0 => {
                        let start = next(&mut state) % (current.len() + 1);
                        let end = start + next(&mut state) % (current.len() - start + 1);
                        current.slice(start..end)
                    }
                    1 => {
                        let at = next(&mut state) % (current.len() + 1);
                        let (left, right) = current.split_at(at);
                        let joined = left.concat(&right);
                        joined.assert_valid();
                        assert_concat_bound(&joined, step, left.len(), right.len());
                        if next(&mut state) & 1 == 0 {
                            left
                        } else {
                            right
                        }
                    }
                    2 => {
                        let b = next(&mut state) % versions.len();
                        if current.len() + versions[b].len() <= 200_000 {
                            let joined = current.concat(&versions[b]);
                            joined.assert_valid();
                            assert_concat_bound(&joined, step, current.len(), versions[b].len());
                            joined
                        } else {
                            current.clone()
                        }
                    }
                    _ => current.push_back(next(&mut state) as i32),
                };

                next_vector.assert_valid();
                if versions.len() == 128 {
                    versions.swap_remove(1 + next(&mut state) % 64);
                }
                versions.push(next_vector);
            }
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(64))]

        #[test]
        fn generated_shapes_preserve_internal_invariants(
            chunks in vec(vec(any::<i16>(), 0..64), 0..64),
            split_points in vec(any::<usize>(), 0..32),
        ) {
            let mut vector = RrbVec::new();
            let mut expected = Vec::new();

            for chunk in chunks {
                expected.extend_from_slice(&chunk);
                vector = vector.concat(&RrbVec::from(chunk));
                vector.assert_valid();
                prop_assert!(vector.iter().copied().eq(expected.iter().copied()));
                prop_assert!(
                    vector.root.as_ref().map_or(0, max_extra_slots)
                        <= node::MAX_EXTRA_SLOTS
                );
            }

            for raw_index in split_points {
                let index = raw_index % (vector.len() + 1);
                let (left, right) = vector.split_at(index);
                left.assert_valid();
                right.assert_valid();
                prop_assert!(
                    left.root.as_ref().map_or(0, max_extra_slots)
                        <= node::MAX_EXTRA_SLOTS + 1
                );
                prop_assert!(
                    right.root.as_ref().map_or(0, max_extra_slots)
                        <= node::MAX_EXTRA_SLOTS + 1
                );

                let joined = left.concat(&right);
                joined.assert_valid();
                prop_assert!(joined.iter().eq(&vector));
                prop_assert!(
                    joined.root.as_ref().map_or(0, max_extra_slots)
                        <= node::MAX_EXTRA_SLOTS
                );
            }
        }
    }
}
