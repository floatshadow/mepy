//! Ordered traversal without flattening the tree.

use std::iter::FusedIterator;
use std::slice;

use super::RrbVec;
use super::node::{Branch, Node, NodeKind};

/// A borrowed iterator over the values in an [`RrbVec`].
pub struct Iter<'a, T> {
    stack: Vec<Frame<'a, T>>,
    current: Option<slice::Iter<'a, T>>,
    tail: Option<slice::Iter<'a, T>>,
    remaining: usize,
}

struct Frame<'a, T> {
    branch: &'a Branch<T>,
    next_child: usize,
}

impl<'a, T> Frame<'a, T> {
    fn take_child(&mut self) -> Option<&'a Node<T>> {
        let child = self.branch.children.get(self.next_child)?;
        self.next_child += 1;
        Some(child)
    }
}

impl<'a, T> Iter<'a, T> {
    pub(super) fn new(vector: &'a RrbVec<T>) -> Self {
        let mut iter = Self {
            stack: Vec::with_capacity(usize::from(vector.height)),
            current: None,
            tail: vector.tail.as_deref().map(|tail| tail.as_leaf().iter()),
            remaining: vector.len,
        };
        if let Some(root) = &vector.root {
            iter.descend(root);
        }
        iter
    }

    fn descend(&mut self, mut node: &'a Node<T>) {
        loop {
            match &node.kind {
                NodeKind::Leaf(values) => {
                    self.current = Some(values.iter());
                    return;
                }
                NodeKind::Branch(branch) => {
                    self.stack.push(Frame {
                        branch,
                        next_child: 1,
                    });
                    node = &branch.children[0];
                }
            }
        }
    }

    fn advance_leaf(&mut self) -> bool {
        while let Some(frame) = self.stack.last_mut() {
            if let Some(child) = frame.take_child() {
                self.descend(child);
                return true;
            }
            self.stack.pop();
        }

        if let Some(tail) = self.tail.take() {
            self.current = Some(tail);
            return true;
        }
        self.current = None;
        false
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(value) = self.current.as_mut().and_then(Iterator::next) {
                self.remaining -= 1;
                return Some(value);
            }
            if !self.advance_leaf() {
                return None;
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}

impl<T> ExactSizeIterator for Iter<'_, T> {
    fn len(&self) -> usize {
        self.remaining
    }
}

impl<T> FusedIterator for Iter<'_, T> {}
