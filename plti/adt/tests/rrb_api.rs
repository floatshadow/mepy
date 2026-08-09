//! Public behavior and boundary tests for `RrbVec`.

use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

use plti_adt::rrb::RrbVec;

fn assert_matches(vector: &RrbVec<i32>, expected: &[i32]) {
    assert_eq!(vector.len(), expected.len());
    assert_eq!(vector.is_empty(), expected.is_empty());
    assert_eq!(vector.first(), expected.first());
    assert_eq!(vector.last(), expected.last());
    assert!(vector.iter().copied().eq(expected.iter().copied()));
    for (index, value) in expected.iter().enumerate() {
        assert_eq!(vector.get(index), Some(value));
        assert_eq!(&vector[index], value);
    }
    assert_eq!(vector.get(expected.len()), None);
}

#[test]
fn construction_and_append_cross_each_radix_boundary() {
    let mut vector = RrbVec::new();
    let mut expected = Vec::new();

    for value in 0..33_000 {
        if matches!(value, 0 | 1 | 31 | 32 | 33 | 1023 | 1024 | 1025 | 32_767) {
            assert_matches(&vector, &expected);
        }
        let previous = vector.clone();
        vector = vector.push_back(value);
        expected.push(value);
        assert_eq!(previous.len() + 1, vector.len());
        assert!(
            previous
                .iter()
                .copied()
                .eq(expected[..expected.len() - 1].iter().copied())
        );
    }
    assert_matches(&vector, &expected);
}

#[test]
fn update_preserves_earlier_versions() {
    let original: RrbVec<_> = (0..5000).collect();
    let mut updated = original.clone();

    for &(index, value) in &[
        (0, -1),
        (31, -2),
        (32, -3),
        (1023, -4),
        (1024, -5),
        (4999, -6),
    ] {
        updated = updated.set(index, value);
        assert_eq!(updated[index], value);
    }

    assert!(original.iter().copied().eq(0..5000));
}

#[test]
fn concat_handles_empty_partial_full_and_unequal_height_inputs() {
    for &(left_len, right_len) in &[
        (0, 0),
        (0, 40),
        (40, 0),
        (1, 1),
        (31, 1),
        (32, 32),
        (33, 1024),
        (1024, 33),
        (7, 32_768),
        (32_768, 7),
    ] {
        let left: RrbVec<_> = (0..left_len).map(|value| value as i32).collect();
        let right: RrbVec<_> = (0..right_len)
            .map(|value| (left_len + value) as i32)
            .collect();
        let joined = left.concat(&right);
        let expected: Vec<_> = (0..left_len + right_len)
            .map(|value| value as i32)
            .collect();

        assert_matches(&joined, &expected);
        assert_eq!(left.len(), left_len);
        assert_eq!(right.len(), right_len);
    }
}

#[test]
fn repeated_small_concatenations_keep_sequence_order() {
    let mut right_growing = RrbVec::new();
    let mut right_expected = Vec::new();
    for chunk_index in 0..600 {
        let len = chunk_index % 47 + 1;
        let chunk: Vec<_> = (0..len).map(|offset| chunk_index * 100 + offset).collect();
        right_expected.extend_from_slice(&chunk);
        right_growing = right_growing.concat(&chunk.into());
    }
    assert_matches(&right_growing, &right_expected);

    let mut left_growing = RrbVec::new();
    let mut left_expected = Vec::new();
    for chunk_index in 0..300 {
        let len = chunk_index % 41 + 1;
        let chunk: Vec<_> = (0..len)
            .map(|offset| -(chunk_index * 100 + offset))
            .collect();
        let mut next_expected = chunk.clone();
        next_expected.extend(left_expected);
        left_expected = next_expected;
        left_growing = RrbVec::from(chunk).concat(&left_growing);
    }
    assert_matches(&left_growing, &left_expected);
}

#[test]
fn every_small_split_matches_slice_split_at() {
    let expected: Vec<_> = (0..257).collect();
    let vector = RrbVec::from(expected.clone());

    for index in 0..=expected.len() {
        let (left, right) = vector.split_at(index);
        assert_matches(&left, &expected[..index]);
        assert_matches(&right, &expected[index..]);
        assert_matches(&left.concat(&right), &expected);
    }
}

#[test]
fn split_crosses_large_tree_boundaries() {
    let expected: Vec<_> = (0..40_000).collect();
    let vector = RrbVec::from(expected.clone());

    for &index in &[
        0, 1, 31, 32, 33, 1023, 1024, 1025, 32_767, 32_768, 32_769, 40_000,
    ] {
        let (left, right) = vector.split_at(index);
        assert_matches(&left, &expected[..index]);
        assert_matches(&right, &expected[index..]);
    }
}

#[test]
fn slices_accept_standard_range_forms() {
    let expected: Vec<_> = (0..200).collect();
    let vector = RrbVec::from(expected.clone());

    assert_matches(&vector.slice(..), &expected);
    assert_matches(&vector.slice(17..), &expected[17..]);
    assert_matches(&vector.slice(..83), &expected[..83]);
    assert_matches(&vector.slice(17..83), &expected[17..83]);
    assert_matches(&vector.slice(17..=82), &expected[17..=82]);
    assert_matches(&vector.slice(50..50), &[]);
}

#[test]
fn insert_matches_vec_at_front_middle_and_back() {
    let mut vector: RrbVec<_> = (0..2000).collect();
    let mut expected: Vec<_> = (0..2000).collect();

    for &(index, value) in &[(0, -1), (32, -2), (1001, -3), (2003, -4)] {
        vector = vector.insert(index, value);
        expected.insert(index, value);
        assert_matches(&vector, &expected);
    }
}

#[test]
fn iterator_tracks_exact_remaining_length() {
    let vector: RrbVec<_> = (0..100).collect();
    let mut iter = vector.iter();
    assert_eq!(iter.len(), 100);
    for expected in 0..100 {
        assert_eq!(iter.next(), Some(&expected));
        assert_eq!(iter.len(), 99 - expected);
    }
    assert_eq!(iter.next(), None);
    assert_eq!(iter.next(), None);
}

#[test]
fn value_traits_follow_sequence_order() {
    let left: RrbVec<_> = (0..100).collect();
    let right = left.slice(..40).concat(&left.slice(40..));
    assert_eq!(left, right);
    assert_eq!(
        format!("{left:?}"),
        format!("{:?}", (0..100).collect::<Vec<_>>())
    );

    let mut left_hash = DefaultHasher::new();
    let mut right_hash = DefaultHasher::new();
    left.hash(&mut left_hash);
    right.hash(&mut right_hash);
    assert_eq!(left_hash.finish(), right_hash.finish());
}

#[test]
fn vector_auto_traits_follow_the_element_type() {
    fn assert_send_sync<T: Send + Sync>() {}
    assert_send_sync::<RrbVec<String>>();
}

#[test]
#[should_panic(expected = "RRB vector index 3 is out of bounds for length 3")]
fn set_rejects_out_of_bounds_index() {
    let vector: RrbVec<_> = (0..3).collect();
    let _ = vector.set(3, 9);
}

#[test]
#[should_panic(expected = "RRB vector split index 4 is out of bounds for length 3")]
fn split_rejects_out_of_bounds_index() {
    let vector: RrbVec<_> = (0..3).collect();
    let _ = vector.split_at(4);
}

#[test]
#[should_panic(expected = "RRB vector range starts at 3 but ends at 2")]
fn slice_rejects_reversed_range() {
    let vector: RrbVec<_> = (0..3).collect();
    let start = 3;
    let end = 2;
    let _ = vector.slice(start..end);
}
