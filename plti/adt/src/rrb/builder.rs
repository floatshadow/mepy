//! Bottom-up construction from owned elements.

use super::node::{BRANCH_FACTOR, Node, SharedNode};

pub(super) struct Built<T> {
    pub(super) len: usize,
    pub(super) height: u8,
    pub(super) root: Option<SharedNode<T>>,
    pub(super) tail: Option<SharedNode<T>>,
}

pub(super) fn from_values<T>(mut values: Vec<T>) -> Built<T> {
    let len = values.len();
    if len == 0 {
        return Built {
            len: 0,
            height: 0,
            root: None,
            tail: None,
        };
    }

    let tail_len = (len - 1) % BRANCH_FACTOR + 1;
    let tail = values.split_off(len - tail_len);
    let (root, height) = build_full_prefix(values);

    Built {
        len,
        height,
        root,
        tail: Some(Node::leaf(tail)),
    }
}

fn build_full_prefix<T>(values: Vec<T>) -> (Option<SharedNode<T>>, u8) {
    if values.is_empty() {
        return (None, 0);
    }
    debug_assert_eq!(values.len() % BRANCH_FACTOR, 0);

    let mut values = values.into_iter();
    let mut level = Vec::with_capacity(values.len().div_ceil(BRANCH_FACTOR));
    loop {
        let leaf: Vec<_> = values.by_ref().take(BRANCH_FACTOR).collect();
        if leaf.is_empty() {
            break;
        }
        level.push(Node::leaf(leaf));
    }

    let mut height = 0u8;
    while level.len() > 1 {
        height = height.checked_add(1).expect("RRB tree height overflow");
        level = pack_branches(level, height);
    }

    (level.pop(), height)
}

fn pack_branches<T>(nodes: Vec<SharedNode<T>>, height: u8) -> Vec<SharedNode<T>> {
    let mut nodes = nodes.into_iter();
    let mut parents = Vec::new();
    loop {
        let children: Vec<_> = nodes.by_ref().take(BRANCH_FACTOR).collect();
        if children.is_empty() {
            break;
        }
        parents.push(Node::branch(children, height));
    }
    parents
}
