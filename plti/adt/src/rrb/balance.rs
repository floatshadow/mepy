//! Pure occupancy planning for RRB node redistribution.

use super::node::{BRANCH_FACTOR, MAX_EXTRA_SLOTS};

pub(super) fn extra_slots(slots: usize, entries: usize) -> usize {
    slots - entries.div_ceil(BRANCH_FACTOR)
}

pub(super) fn packed_extra_slots(counts: &[usize]) -> usize {
    counts
        .chunks(BRANCH_FACTOR)
        .map(|chunk| extra_slots(chunk.len(), chunk.iter().sum()))
        .max()
        .unwrap_or(0)
}

pub(super) fn target_node_count<const WIDTH: usize>(
    entry_counts: &[usize],
    max_extra: usize,
) -> Option<usize> {
    assert!(WIDTH > 0, "RRB branch width must be positive");
    let total: usize = entry_counts.iter().sum();
    assert!(total > 0, "cannot rebalance empty RRB nodes");
    assert!(
        entry_counts
            .iter()
            .all(|&count| (1..=WIDTH).contains(&count)),
        "RRB entry count exceeds the branch width"
    );

    let target = total
        .div_ceil(WIDTH)
        .checked_add(max_extra)
        .expect("RRB redistribution size overflow");
    (entry_counts.len() > target).then_some(target)
}

pub(super) fn packed_sizes<const WIDTH: usize>(total: usize, node_count: usize) -> Vec<usize> {
    assert!(WIDTH > 0, "RRB branch width must be positive");
    assert!(total > 0, "cannot pack an empty RRB node group");
    assert!(node_count > 0, "an RRB node group needs a node");
    assert!(
        total <= node_count * WIDTH,
        "RRB node group exceeds its capacity"
    );
    assert!(node_count <= total, "RRB nodes cannot be empty");

    let mut remaining = total;
    let mut sizes = Vec::with_capacity(node_count);
    for remaining_nodes in (1..=node_count).rev() {
        let size = WIDTH.min(remaining - (remaining_nodes - 1));
        sizes.push(size);
        remaining -= size;
    }
    debug_assert_eq!(remaining, 0);
    sizes
}

pub(super) fn choose_shuffle_interval(
    counts: &[usize],
    seam: usize,
    target: usize,
) -> Option<(usize, usize, usize)> {
    let mut best = None;
    for lo in 0..counts.len() {
        for hi in lo + 1..=counts.len() {
            let crosses_seam = match seam {
                0 => lo == 0,
                seam if seam == counts.len() => hi == counts.len(),
                seam => lo < seam && seam < hi,
            };
            if !crosses_seam {
                continue;
            }

            let outside = counts.len() - (hi - lo);
            if outside >= target {
                continue;
            }
            let interval_target = target - outside;
            let entries: usize = counts[lo..hi].iter().sum();
            if !(entries.div_ceil(BRANCH_FACTOR)..=entries).contains(&interval_target) {
                continue;
            }

            let packed = packed_sizes::<BRANCH_FACTOR>(entries, interval_target);
            let mut result_counts = Vec::with_capacity(target);
            result_counts.extend_from_slice(&counts[..lo]);
            result_counts.extend_from_slice(&packed);
            result_counts.extend_from_slice(&counts[hi..]);
            if packed_extra_slots(&result_counts) > MAX_EXTRA_SLOTS {
                continue;
            }

            let cost = (entries, hi - lo);
            if best.as_ref().is_none_or(|(best_cost, _)| cost < *best_cost) {
                best = Some((cost, (lo, hi, interval_target)));
            }
        }
    }
    best.map(|(_, interval)| interval)
}

pub(super) fn greedy_partition(nested_prefix: &[usize], node_count: usize) -> Option<Vec<usize>> {
    let entry_count = nested_prefix.len() - 1;
    if node_count == 0 || node_count > entry_count || entry_count > node_count * BRANCH_FACTOR {
        return None;
    }

    // Removing an entry from either end of a valid group cannot increase its
    // extra-slot count. A longest valid prefix leaves the easiest suffix.
    let mut sizes = Vec::with_capacity(node_count);
    let mut start = 0usize;
    for remaining_nodes in (1..=node_count).rev() {
        let maximum = BRANCH_FACTOR.min(entry_count - start - (remaining_nodes - 1));
        let size = (1..=maximum)
            .rev()
            .find(|&size| {
                let nested_entries = nested_prefix[start + size] - nested_prefix[start];
                extra_slots(size, nested_entries) <= MAX_EXTRA_SLOTS
            })
            .expect("a single entry always satisfies the extra-slot bound");
        if entry_count - start - size > (remaining_nodes - 1) * BRANCH_FACTOR {
            return None;
        }
        sizes.push(size);
        start += size;
    }
    (start == entry_count).then_some(sizes)
}

#[cfg(test)]
mod tests {
    use super::{choose_shuffle_interval, greedy_partition, packed_sizes, target_node_count};

    #[test]
    fn figure_7_requires_one_fewer_node_when_e_is_one() {
        let count = target_node_count::<4>(&[4, 3, 1, 3, 3, 2], 1);
        assert_eq!(count, Some(5));
        assert_eq!(packed_sizes::<4>(16, count.unwrap()), [4, 4, 4, 3, 1]);
    }

    #[test]
    fn figure_8_needs_no_redistribution_when_e_is_one() {
        assert_eq!(target_node_count::<4>(&[4, 3, 2, 2], 1), None);
    }

    #[test]
    fn production_error_bound_accepts_figure_7_shape() {
        assert_eq!(target_node_count::<32>(&[32, 31, 30, 32, 31, 30], 2), None);
    }

    #[test]
    fn greedy_partition_matches_exhaustive_search() {
        fn can_partition(prefix: &[usize], start: usize, groups: usize) -> bool {
            let entry_count = prefix.len() - 1;
            if groups == 0 {
                return start == entry_count;
            }
            if entry_count - start < groups {
                return false;
            }

            let maximum = super::BRANCH_FACTOR.min(entry_count - start - (groups - 1));
            (1..=maximum).any(|size| {
                let entries = prefix[start + size] - prefix[start];
                super::extra_slots(size, entries) <= super::MAX_EXTRA_SLOTS
                    && can_partition(prefix, start + size, groups - 1)
            })
        }

        const WEIGHTS: [usize; 4] = [1, 2, 31, 32];
        for len in 1..=7 {
            for mut shape in 0..4usize.pow(len as u32) {
                let mut prefix = vec![0];
                for _ in 0..len {
                    let weight = WEIGHTS[shape % WEIGHTS.len()];
                    shape /= WEIGHTS.len();
                    prefix.push(prefix.last().copied().unwrap() + weight);
                }

                for groups in 1..=len {
                    assert_eq!(
                        greedy_partition(&prefix, groups).is_some(),
                        can_partition(&prefix, 0, groups),
                        "prefix {prefix:?}, groups {groups}"
                    );
                }
            }
        }
    }

    #[test]
    fn shuffle_keeps_valid_nodes_outside_the_seam_window() {
        assert_eq!(
            choose_shuffle_interval(&[32, 2, 10, 6, 3], 0, 4),
            Some((0, 3, 2))
        );
    }
}
