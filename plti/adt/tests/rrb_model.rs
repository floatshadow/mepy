//! Generated operation sequences checked against `Vec`.

use plti_adt::rrb::RrbVec;
use proptest::collection::vec;
use proptest::prelude::*;

#[derive(Clone, Debug)]
enum Operation {
    Push(i16),
    Set(usize, i16),
    ConcatRight(Vec<i16>),
    ConcatLeft(Vec<i16>),
    KeepLeft(usize),
    KeepRight(usize),
    Slice(usize, usize),
    Insert(usize, i16),
}

fn operation() -> impl Strategy<Value = Operation> {
    prop_oneof![
        any::<i16>().prop_map(Operation::Push),
        (any::<usize>(), any::<i16>()).prop_map(|(index, value)| Operation::Set(index, value)),
        vec(any::<i16>(), 0..48).prop_map(Operation::ConcatRight),
        vec(any::<i16>(), 0..48).prop_map(Operation::ConcatLeft),
        any::<usize>().prop_map(Operation::KeepLeft),
        any::<usize>().prop_map(Operation::KeepRight),
        (any::<usize>(), any::<usize>()).prop_map(|(start, end)| Operation::Slice(start, end)),
        (any::<usize>(), any::<i16>()).prop_map(|(index, value)| Operation::Insert(index, value)),
    ]
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(128))]

    #[test]
    fn generated_operations_match_vec(operations in vec(operation(), 0..120)) {
        let mut vector = RrbVec::new();
        let mut model = Vec::new();

        for operation in operations {
            let old_vector = vector.clone();
            let old_model = model.clone();

            match operation {
                Operation::Push(value) => {
                    vector = vector.push_back(value);
                    model.push(value);
                }
                Operation::Set(raw_index, value) if !model.is_empty() => {
                    let index = raw_index % model.len();
                    vector = vector.set(index, value);
                    model[index] = value;
                }
                Operation::Set(_, _) => {}
                Operation::ConcatRight(values) => {
                    vector = vector.concat(&RrbVec::from(values.clone()));
                    model.extend(values);
                }
                Operation::ConcatLeft(values) => {
                    vector = RrbVec::from(values.clone()).concat(&vector);
                    let mut joined = values;
                    joined.extend(model);
                    model = joined;
                }
                Operation::KeepLeft(raw_index) => {
                    let index = raw_index % (model.len() + 1);
                    vector = vector.split_at(index).0;
                    model.truncate(index);
                }
                Operation::KeepRight(raw_index) => {
                    let index = raw_index % (model.len() + 1);
                    vector = vector.split_at(index).1;
                    model = model.split_off(index);
                }
                Operation::Slice(raw_start, raw_end) => {
                    let first = raw_start % (model.len() + 1);
                    let second = raw_end % (model.len() + 1);
                    let start = first.min(second);
                    let end = first.max(second);
                    vector = vector.slice(start..end);
                    model = model[start..end].to_vec();
                }
                Operation::Insert(raw_index, value) => {
                    let index = raw_index % (model.len() + 1);
                    vector = vector.insert(index, value);
                    model.insert(index, value);
                }
            }

            prop_assert!(old_vector.iter().copied().eq(old_model.iter().copied()));
            prop_assert_eq!(vector.len(), model.len());
            prop_assert!(vector.iter().copied().eq(model.iter().copied()));
            prop_assert_eq!(vector.first(), model.first());
            prop_assert_eq!(vector.last(), model.last());
            prop_assert_eq!(vector.get(model.len()), None);
        }
    }
}
