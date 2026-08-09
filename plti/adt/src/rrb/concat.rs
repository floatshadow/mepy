//! Edge merging, node redistribution, and concatenation balancing.

use std::sync::Arc;

use super::balance::{
    choose_shuffle_interval, extra_slots, greedy_partition,
    packed_extra_slots as packed_extra_counts, packed_sizes, target_node_count,
};
use super::node::{BRANCH_FACTOR, MAX_EXTRA_SLOTS, Node, SharedNode, normalize_root};

struct Frontier<T> {
    nodes: Vec<SharedNode<T>>,
    seam: usize,
}

pub(super) fn append_leaf<T: Clone>(
    root: Option<SharedNode<T>>,
    height: u8,
    leaf: SharedNode<T>,
) -> (Option<SharedNode<T>>, u8) {
    let Some(root) = root else {
        return (Some(leaf), 0);
    };

    let mut frontier = append_leaf_at_height(root, height, leaf);
    if frontier.nodes.len() == 1 {
        return (frontier.nodes.pop(), height);
    }

    let new_height = height.checked_add(1).expect("RRB tree height overflow");
    (Some(Node::branch(frontier.nodes, new_height)), new_height)
}

fn append_leaf_at_height<T: Clone>(
    root: SharedNode<T>,
    height: u8,
    leaf: SharedNode<T>,
) -> Frontier<T> {
    if height == 0 {
        return Frontier {
            nodes: vec![root, leaf],
            seam: 1,
        };
    }

    let branch = root.as_branch();
    let mut children = branch.children.to_vec();
    let rightmost = children.pop().expect("an RRB branch is non-empty");
    let boundary = append_leaf_at_height(rightmost, height - 1, leaf);
    let seam = children.len() + boundary.seam;
    children.extend(boundary.nodes);
    rebuild_parent(children, seam, height)
}

pub(super) fn concat_roots<T: Clone>(
    left: SharedNode<T>,
    left_height: u8,
    right: SharedNode<T>,
    right_height: u8,
) -> (SharedNode<T>, u8) {
    let height = left_height.max(right_height);
    let mut frontier = concat_nodes(left, left_height, right, right_height);
    if frontier.nodes.len() > 1 {
        frontier = rebalance_group(frontier, height);
    }
    let (root, root_height) = if frontier.nodes.len() == 1 {
        (
            frontier.nodes.pop().expect("concatenation produced a root"),
            height,
        )
    } else {
        let root_height = height.checked_add(1).expect("RRB tree height overflow");
        (Node::branch(frontier.nodes, root_height), root_height)
    };
    let (root, root_height) = normalize_root(Some(root), root_height);
    (
        root.expect("concatenating non-empty trees produces a root"),
        root_height,
    )
}

fn concat_nodes<T: Clone>(
    left: SharedNode<T>,
    left_height: u8,
    right: SharedNode<T>,
    right_height: u8,
) -> Frontier<T> {
    // Only the touching child pair descends. Siblings are cloned as Arc
    // pointers and remain structurally shared.
    match left_height.cmp(&right_height) {
        std::cmp::Ordering::Equal if left_height == 0 => merge_leaves(&left, &right),
        std::cmp::Ordering::Equal => {
            let left_branch = left.as_branch();
            let right_branch = right.as_branch();

            let mut candidates =
                Vec::with_capacity(left_branch.children.len() + right_branch.children.len());
            candidates.extend_from_slice(&left_branch.children[..left_branch.children.len() - 1]);

            let middle = concat_nodes(
                Arc::clone(left_branch.children.last().expect("non-empty branch")),
                left_height - 1,
                Arc::clone(&right_branch.children[0]),
                right_height - 1,
            );
            let seam = candidates.len() + middle.seam;
            candidates.extend(middle.nodes);
            candidates.extend_from_slice(&right_branch.children[1..]);

            rebuild_parent(candidates, seam, left_height)
        }
        std::cmp::Ordering::Greater => {
            let left_branch = left.as_branch();
            let mut candidates = Vec::with_capacity(left_branch.children.len() + 1);
            candidates.extend_from_slice(&left_branch.children[..left_branch.children.len() - 1]);
            let boundary = concat_nodes(
                Arc::clone(left_branch.children.last().expect("non-empty branch")),
                left_height - 1,
                right,
                right_height,
            );
            let seam = candidates.len() + boundary.seam;
            candidates.extend(boundary.nodes);

            rebuild_parent(candidates, seam, left_height)
        }
        std::cmp::Ordering::Less => {
            let right_branch = right.as_branch();
            let mut candidates = Vec::with_capacity(right_branch.children.len() + 1);
            let boundary = concat_nodes(
                left,
                left_height,
                Arc::clone(&right_branch.children[0]),
                right_height - 1,
            );
            let seam = boundary.seam;
            candidates.extend(boundary.nodes);
            candidates.extend_from_slice(&right_branch.children[1..]);

            rebuild_parent(candidates, seam, right_height)
        }
    }
}

fn rebuild_parent<T: Clone>(nodes: Vec<SharedNode<T>>, seam: usize, height: u8) -> Frontier<T> {
    pack_parent_level(
        rebalance_group(Frontier { nodes, seam }, height - 1),
        height,
    )
}

fn merge_leaves<T: Clone>(left: &SharedNode<T>, right: &SharedNode<T>) -> Frontier<T> {
    if left.len == BRANCH_FACTOR {
        return Frontier {
            nodes: vec![Arc::clone(left), Arc::clone(right)],
            seam: 1,
        };
    }

    let total = left
        .len
        .checked_add(right.len)
        .expect("RRB vector length overflow");
    let mut values = Vec::with_capacity(total);
    values.extend_from_slice(left.as_leaf());
    values.extend_from_slice(right.as_leaf());
    let sizes = packed_sizes::<BRANCH_FACTOR>(total, total.div_ceil(BRANCH_FACTOR));
    let seam = map_seam(&sizes, left.len);
    Frontier {
        nodes: pack_leaf_values(values, &sizes),
        seam,
    }
}

fn rebalance_group<T: Clone>(frontier: Frontier<T>, node_height: u8) -> Frontier<T> {
    let Frontier { nodes, seam } = frontier;
    let counts: Vec<_> = nodes.iter().map(|node| node.entry_count()).collect();
    let target = match target_node_count::<BRANCH_FACTOR>(&counts, MAX_EXTRA_SLOTS) {
        Some(target) => target,
        None if packed_extra_slots(&nodes) > MAX_EXTRA_SLOTS => nodes.len(),
        None => return Frontier { nodes, seam },
    };
    let (lo, hi, interval_target) = choose_shuffle_interval(&counts, seam, target)
        .expect("the complete boundary window can always be redistributed");
    let interval_seam = seam.saturating_sub(lo).min(hi - lo);
    let interval_total: usize = counts[lo..hi].iter().sum();

    if node_height == 0 {
        let value_seam: usize = nodes[lo..lo + interval_seam]
            .iter()
            .map(|node| node.len)
            .sum();
        let mut values = Vec::with_capacity(interval_total);
        for node in &nodes[lo..hi] {
            values.extend_from_slice(node.as_leaf());
        }
        let sizes = packed_sizes::<BRANCH_FACTOR>(interval_total, interval_target);
        let rebalanced = pack_leaf_values(values, &sizes);
        return splice_frontier(nodes, lo, hi, rebalanced, map_seam(&sizes, value_seam));
    }

    let mut entry_seam: usize = counts[lo..lo + interval_seam].iter().sum();
    let mut entries = Vec::with_capacity(interval_total);
    for node in &nodes[lo..hi] {
        entries.extend_from_slice(&node.as_branch().children);
    }

    let node_sizes = match choose_branch_partition(
        &entries,
        interval_target,
        &counts[..lo],
        &counts[hi..],
    ) {
        Some(node_sizes) => node_sizes,
        None => {
            (entries, entry_seam) = repair_lower_window(entries, node_height - 1, entry_seam);
            let repaired_target = interval_target.min(
                entries
                    .len()
                    .div_ceil(BRANCH_FACTOR)
                    .saturating_add(MAX_EXTRA_SLOTS),
            );
            choose_branch_partition(
                &entries,
                repaired_target,
                &counts[..lo],
                &counts[hi..],
            )
            .unwrap_or_else(|| {
                let counts: Vec<_> = entries.iter().map(|node| node.entry_count()).collect();
                panic!(
                    "bounded lower repair failed at height {node_height}, seam {entry_seam}, counts {counts:?}"
                )
            })
        }
    };
    let rebalanced = pack_branch_entries(entries, node_height, &node_sizes);
    debug_assert!(
        rebalanced
            .iter()
            .all(|node| local_extra_slots(node) <= MAX_EXTRA_SLOTS),
        "RRB redistribution created an invalid child node"
    );
    splice_frontier(nodes, lo, hi, rebalanced, map_seam(&node_sizes, entry_seam))
}

fn splice_frontier<T>(
    nodes: Vec<SharedNode<T>>,
    lo: usize,
    hi: usize,
    replacement: Vec<SharedNode<T>>,
    replacement_seam: usize,
) -> Frontier<T> {
    let mut result = Vec::with_capacity(nodes.len() - (hi - lo) + replacement.len());
    let mut nodes = nodes.into_iter();
    result.extend(nodes.by_ref().take(lo));
    let seam = result.len() + replacement_seam;
    result.extend(replacement);
    for _ in lo..hi {
        nodes.next();
    }
    result.extend(nodes);
    debug_assert!(packed_extra_slots(&result) <= MAX_EXTRA_SLOTS);
    Frontier {
        nodes: result,
        seam,
    }
}

fn choose_branch_partition<T>(
    entries: &[SharedNode<T>],
    preferred_nodes: usize,
    before: &[usize],
    after: &[usize],
) -> Option<Vec<usize>> {
    let minimum = entries.len().div_ceil(BRANCH_FACTOR);
    let mut nested_prefix = Vec::with_capacity(entries.len() + 1);
    nested_prefix.push(0usize);
    for entry in entries {
        let total = nested_prefix
            .last()
            .copied()
            .expect("the prefix has an initial value")
            .checked_add(entry.entry_count())
            .expect("RRB entry count overflow");
        nested_prefix.push(total);
    }

    for node_count in (minimum..=preferred_nodes).rev() {
        let Some(sizes) = greedy_partition(&nested_prefix, node_count) else {
            continue;
        };
        let mut result_counts = Vec::with_capacity(before.len() + sizes.len() + after.len());
        result_counts.extend_from_slice(before);
        result_counts.extend_from_slice(&sizes);
        result_counts.extend_from_slice(after);
        if packed_extra_counts(&result_counts) <= MAX_EXTRA_SLOTS {
            return Some(sizes);
        }
    }
    None
}

fn repair_lower_window<T: Clone>(
    mut entries: Vec<SharedNode<T>>,
    node_height: u8,
    seam: usize,
) -> (Vec<SharedNode<T>>, usize) {
    let window_width = 2 * BRANCH_FACTOR;
    let window_start = seam.saturating_sub(BRANCH_FACTOR);
    let window_end = entries.len().min(window_start.saturating_add(window_width));
    let window_start = window_end.saturating_sub(window_width);
    let repaired = rebalance_group(
        Frontier {
            nodes: entries[window_start..window_end].to_vec(),
            seam: seam
                .saturating_sub(window_start)
                .min(window_end - window_start),
        },
        node_height,
    );
    let repaired_seam = window_start + repaired.seam;
    entries.splice(window_start..window_end, repaired.nodes);
    (entries, repaired_seam)
}

fn local_extra_slots<T>(node: &SharedNode<T>) -> usize {
    let branch = node.as_branch();
    let nested_entries: usize = branch
        .children
        .iter()
        .map(|child| child.entry_count())
        .sum();
    extra_slots(branch.children.len(), nested_entries)
}

fn packed_extra_slots<T>(nodes: &[SharedNode<T>]) -> usize {
    let counts: Vec<_> = nodes.iter().map(|node| node.entry_count()).collect();
    packed_extra_counts(&counts)
}

fn pack_leaf_values<T>(values: Vec<T>, sizes: &[usize]) -> Vec<SharedNode<T>> {
    debug_assert_eq!(values.len(), sizes.iter().sum());
    let mut values = values.into_iter();
    sizes
        .iter()
        .map(|&size| Node::leaf(values.by_ref().take(size).collect()))
        .collect()
}

fn pack_branch_entries<T>(
    entries: Vec<SharedNode<T>>,
    height: u8,
    sizes: &[usize],
) -> Vec<SharedNode<T>> {
    debug_assert_eq!(entries.len(), sizes.iter().sum());
    let mut entries = entries.into_iter();
    sizes
        .iter()
        .map(|&size| Node::branch(entries.by_ref().take(size).collect(), height))
        .collect()
}

fn pack_parent_level<T>(frontier: Frontier<T>, height: u8) -> Frontier<T> {
    let count = frontier.nodes.len();
    let sizes = packed_sizes::<BRANCH_FACTOR>(count, count.div_ceil(BRANCH_FACTOR));
    Frontier {
        nodes: pack_branch_entries(frontier.nodes, height, &sizes),
        seam: map_seam(&sizes, frontier.seam),
    }
}

fn map_seam(sizes: &[usize], seam: usize) -> usize {
    let mut end = 0;
    for (index, size) in sizes.iter().enumerate() {
        end += size;
        if end > seam {
            return index;
        }
    }
    sizes.len()
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::super::node::Node;
    use super::merge_leaves;

    #[test]
    fn merging_a_full_left_leaf_keeps_both_leaves_shared() {
        let left = Node::leaf((0..32).collect());
        let right = Node::leaf((32..64).collect());

        let merged = merge_leaves(&left, &right);

        assert_eq!(merged.nodes.len(), 2);
        assert_eq!(merged.seam, 1);
        assert!(Arc::ptr_eq(&merged.nodes[0], &left));
        assert!(Arc::ptr_eq(&merged.nodes[1], &right));
    }
}
