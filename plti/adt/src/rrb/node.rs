//! Internal nodes, size tables, and radix navigation.

use std::sync::Arc;

pub(super) const BRANCH_BITS: u32 = 5;
pub(super) const BRANCH_FACTOR: usize = 1 << BRANCH_BITS;
pub(super) const MAX_EXTRA_SLOTS: usize = 2;

pub(super) type SharedNode<T> = Arc<Node<T>>;

pub(super) struct Node<T> {
    pub(super) len: usize,
    pub(super) kind: NodeKind<T>,
}

pub(super) enum NodeKind<T> {
    Leaf(Box<[T]>),
    Branch(Branch<T>),
}

pub(super) struct Branch<T> {
    pub(super) children: Box<[SharedNode<T>]>,
    pub(super) sizes: Option<Box<[usize]>>,
}

impl<T> Node<T> {
    pub(super) fn leaf(values: Vec<T>) -> SharedNode<T> {
        assert!(
            (1..=BRANCH_FACTOR).contains(&values.len()),
            "an RRB leaf must contain between 1 and {BRANCH_FACTOR} values"
        );
        Arc::new(Self {
            len: values.len(),
            kind: NodeKind::Leaf(values.into_boxed_slice()),
        })
    }

    pub(super) fn branch(children: Vec<SharedNode<T>>, height: u8) -> SharedNode<T> {
        assert!(height > 0, "an RRB branch must be above leaf height");
        assert!(
            (1..=BRANCH_FACTOR).contains(&children.len()),
            "an RRB branch must contain between 1 and {BRANCH_FACTOR} children"
        );

        let full_child_len = child_capacity(height);
        let is_regular = children
            .iter()
            .take(children.len().saturating_sub(1))
            .all(|child| child.len == full_child_len);
        let total = children
            .iter()
            .try_fold(0usize, |total, child| total.checked_add(child.len));
        let total = total.expect("RRB vector length overflow");
        let sizes = if is_regular {
            None
        } else {
            let mut total = 0usize;
            Some(
                children
                    .iter()
                    .map(|child| {
                        total += child.len;
                        total
                    })
                    .collect::<Vec<_>>()
                    .into_boxed_slice(),
            )
        };

        Arc::new(Self {
            len: total,
            kind: NodeKind::Branch(Branch {
                children: children.into_boxed_slice(),
                sizes,
            }),
        })
    }

    pub(super) fn as_leaf(&self) -> &[T] {
        match &self.kind {
            NodeKind::Leaf(values) => values,
            NodeKind::Branch(_) => panic!("expected an RRB leaf"),
        }
    }

    pub(super) fn as_branch(&self) -> &Branch<T> {
        match &self.kind {
            NodeKind::Leaf(_) => panic!("expected an RRB branch"),
            NodeKind::Branch(branch) => branch,
        }
    }

    pub(super) fn entry_count(&self) -> usize {
        match &self.kind {
            NodeKind::Leaf(values) => values.len(),
            NodeKind::Branch(branch) => branch.children.len(),
        }
    }
}

pub(super) fn child_capacity(branch_height: u8) -> usize {
    let shift = BRANCH_BITS.saturating_mul(u32::from(branch_height));
    if shift >= usize::BITS {
        usize::MAX
    } else {
        1usize << shift
    }
}

pub(super) fn get<T>(mut node: &Node<T>, mut height: u8, mut index: usize) -> &T {
    debug_assert!(index < node.len);

    loop {
        match &node.kind {
            NodeKind::Leaf(values) => return &values[index],
            NodeKind::Branch(branch) => {
                debug_assert!(height > 0);
                let (child_index, child_offset) = locate_child(branch, height, index);
                node = &branch.children[child_index];
                height -= 1;
                index -= child_offset;
            }
        }
    }
}

pub(super) fn locate_child<T>(branch: &Branch<T>, height: u8, index: usize) -> (usize, usize) {
    let shift = BRANCH_BITS * u32::from(height);
    let radix_index = if shift >= usize::BITS {
        0
    } else {
        index >> shift
    };

    match &branch.sizes {
        None => {
            let child_index = radix_index;
            let child_offset = child_index * child_capacity(height);
            (child_index, child_offset)
        }
        Some(sizes) => {
            let mut child_index = radix_index.min(sizes.len() - 1);
            while index >= sizes[child_index] {
                child_index += 1;
            }
            let child_offset = child_index
                .checked_sub(1)
                .map_or(0, |previous| sizes[previous]);
            (child_index, child_offset)
        }
    }
}

pub(super) fn updated<T: Clone>(
    node: &SharedNode<T>,
    height: u8,
    index: usize,
    value: T,
) -> SharedNode<T> {
    match &node.kind {
        NodeKind::Leaf(values) => {
            let mut new_values = values.to_vec();
            new_values[index] = value;
            Node::leaf(new_values)
        }
        NodeKind::Branch(branch) => {
            let (child_index, child_offset) = locate_child(branch, height, index);
            let mut children = branch.children.to_vec();
            children[child_index] = updated(
                &children[child_index],
                height - 1,
                index - child_offset,
                value,
            );
            Node::branch(children, height)
        }
    }
}

pub(super) fn split<T: Clone>(
    node: &SharedNode<T>,
    height: u8,
    index: usize,
) -> (Option<SharedNode<T>>, Option<SharedNode<T>>) {
    debug_assert!(index <= node.len);
    if index == 0 {
        return (None, Some(Arc::clone(node)));
    }
    if index == node.len {
        return (Some(Arc::clone(node)), None);
    }

    match &node.kind {
        NodeKind::Leaf(values) => (
            Some(Node::leaf(values[..index].to_vec())),
            Some(Node::leaf(values[index..].to_vec())),
        ),
        NodeKind::Branch(branch) => {
            let (child_index, child_offset) = locate_child(branch, height, index);
            let (left_boundary, right_boundary) = split(
                &branch.children[child_index],
                height - 1,
                index - child_offset,
            );

            let mut left = branch.children[..child_index].to_vec();
            left.extend(left_boundary);

            let mut right = Vec::with_capacity(branch.children.len() - child_index);
            right.extend(right_boundary);
            right.extend_from_slice(&branch.children[child_index + 1..]);

            (
                (!left.is_empty()).then(|| Node::branch(left, height)),
                (!right.is_empty()).then(|| Node::branch(right, height)),
            )
        }
    }
}

pub(super) fn normalize_root<T>(
    mut root: Option<SharedNode<T>>,
    mut height: u8,
) -> (Option<SharedNode<T>>, u8) {
    while height > 0 {
        let Some(node) = root.as_ref() else {
            return (None, 0);
        };
        let branch = node.as_branch();
        if branch.children.len() != 1 {
            break;
        }
        root = Some(Arc::clone(&branch.children[0]));
        height -= 1;
    }
    (root, height)
}

pub(super) fn compact_root<T: Clone>(
    root: Option<SharedNode<T>>,
    height: u8,
    max_extra_slots: usize,
) -> (Option<SharedNode<T>>, u8) {
    let (mut root, mut height) = normalize_root(root, height);

    loop {
        let Some(node) = root.as_ref() else {
            return (None, 0);
        };
        if height == 0 {
            return (root, 0);
        }

        let branch = node.as_branch();
        if height == 1 {
            if node.len > BRANCH_FACTOR {
                return (root, height);
            }
            let mut values = Vec::with_capacity(node.len);
            for child in &branch.children {
                values.extend_from_slice(child.as_leaf());
            }
            return (Some(Node::leaf(values)), 0);
        }

        let grandchild_count: usize = branch
            .children
            .iter()
            .map(|child| child.as_branch().children.len())
            .sum();
        if grandchild_count > BRANCH_FACTOR {
            return (root, height);
        }

        let mut grandchildren = Vec::with_capacity(grandchild_count);
        for child in &branch.children {
            grandchildren.extend_from_slice(&child.as_branch().children);
        }
        if child_extra_slots(&grandchildren) > max_extra_slots {
            return (root, height);
        }
        height -= 1;
        root = Some(Node::branch(grandchildren, height));
        (root, height) = normalize_root(root, height);
    }
}

fn child_extra_slots<T>(children: &[SharedNode<T>]) -> usize {
    let entries: usize = children.iter().map(|child| child.entry_count()).sum();
    children.len() - entries.div_ceil(BRANCH_FACTOR)
}

#[cfg(test)]
pub(super) fn assert_valid<T>(node: &SharedNode<T>, height: u8, is_root: bool) -> usize {
    match (&node.kind, height) {
        (NodeKind::Leaf(values), 0) => {
            assert!((1..=BRANCH_FACTOR).contains(&values.len()));
            assert_eq!(node.len, values.len());
            values.len()
        }
        (NodeKind::Branch(branch), 1..) => {
            assert!((1..=BRANCH_FACTOR).contains(&branch.children.len()));
            if is_root {
                assert_ne!(branch.children.len(), 1, "a root branch must be collapsed");
            }

            let child_lengths: Vec<_> = branch
                .children
                .iter()
                .map(|child| assert_valid(child, height - 1, false))
                .collect();
            let total: usize = child_lengths.iter().sum();
            assert_eq!(node.len, total);

            let full_child_len = child_capacity(height);
            let regular = child_lengths
                .iter()
                .take(child_lengths.len().saturating_sub(1))
                .all(|&len| len == full_child_len);

            match &branch.sizes {
                None => assert!(regular, "a branch without sizes must be regular"),
                Some(sizes) => {
                    assert!(!regular, "a regular branch must omit its size table");
                    assert_eq!(sizes.len(), branch.children.len());
                    let mut cumulative = 0;
                    for (&size, &child_len) in sizes.iter().zip(&child_lengths) {
                        cumulative += child_len;
                        assert_eq!(size, cumulative);
                    }
                }
            }
            total
        }
        (NodeKind::Leaf(_), _) => panic!("a leaf must have height zero"),
        (NodeKind::Branch(_), 0) => panic!("a branch must have positive height"),
    }
}

#[cfg(test)]
pub(super) fn max_extra_slots<T>(node: &SharedNode<T>) -> usize {
    match &node.kind {
        NodeKind::Leaf(_) => 0,
        NodeKind::Branch(branch) => {
            let entries: usize = branch
                .children
                .iter()
                .map(|child| child.entry_count())
                .sum();
            let local = branch.children.len() - entries.div_ceil(BRANCH_FACTOR);
            branch
                .children
                .iter()
                .map(max_extra_slots)
                .fold(local, usize::max)
        }
    }
}

#[cfg(test)]
pub(super) fn assert_extra_slots<T>(
    node: &SharedNode<T>,
    on_left_edge: bool,
    on_right_edge: bool,
    left_debt: bool,
    right_debt: bool,
) {
    let NodeKind::Branch(branch) = &node.kind else {
        return;
    };
    let entries: usize = branch
        .children
        .iter()
        .map(|child| child.entry_count())
        .sum();
    let local = branch.children.len() - entries.div_ceil(BRANCH_FACTOR);
    let allowed = MAX_EXTRA_SLOTS
        + usize::from(on_left_edge && left_debt)
        + usize::from(on_right_edge && right_debt);
    assert!(
        local <= allowed,
        "RRB node has {local} extra slots but its edge allows {allowed}"
    );

    let last = branch.children.len() - 1;
    for (index, child) in branch.children.iter().enumerate() {
        assert_extra_slots(
            child,
            on_left_edge && index == 0,
            on_right_edge && index == last,
            left_debt,
            right_debt,
        );
    }
}

#[cfg(test)]
pub(super) fn contains_ptr<T>(root: &SharedNode<T>, target: &SharedNode<T>) -> bool {
    if Arc::ptr_eq(root, target) {
        return true;
    }
    match &root.kind {
        NodeKind::Leaf(_) => false,
        NodeKind::Branch(branch) => branch
            .children
            .iter()
            .any(|child| contains_ptr(child, target)),
    }
}

#[cfg(test)]
mod tests {
    use super::{MAX_EXTRA_SLOTS, Node, assert_extra_slots, compact_root, max_extra_slots};

    #[test]
    fn root_compaction_keeps_the_split_debt_bound() {
        let leaves: Vec<_> = (0..5).map(|value| Node::leaf(vec![value])).collect();
        let left = Node::branch(leaves[..2].to_vec(), 1);
        let right = Node::branch(leaves[2..].to_vec(), 1);
        let root = Node::branch(vec![left, right], 2);

        let (_, height) = compact_root(Some(root), 2, MAX_EXTRA_SLOTS + 1);

        assert_eq!(height, 2);
    }

    #[test]
    fn overlapping_cut_edges_add_their_debt() {
        let counts = [2, 2, 1, 32, 17, 7];
        let children = counts
            .into_iter()
            .map(|count| {
                let leaves = (0..count).map(|_| Node::leaf(vec![0; 32])).collect();
                Node::branch(leaves, 1)
            })
            .collect();
        let root = Node::branch(children, 2);

        assert_eq!(max_extra_slots(&root), MAX_EXTRA_SLOTS + 2);
        assert_extra_slots(&root, true, true, true, true);
    }
}
