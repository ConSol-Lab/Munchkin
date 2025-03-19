#![cfg(test)]

use drcp_format::Comparison::*;

use super::test_step_checker;
use super::Validity;
use crate::model::Model;
use crate::proof::checking;
use crate::proof::checking::atomic;
use crate::proof::checking::Atomic;

#[test]
fn valid_binary_decomposition() {
    test_all_different_checker(
        vec![atomic("array_1", Equal, 5)],
        Some(atomic("array_2", NotEqual, 5)),
        Validity::Valid,
    );
}

#[test]
fn valid_bounds_explanation() {
    let premises = (1..=3)
        .flat_map(|i| {
            [
                atomic(format!("array_{i}"), GreaterThanEqual, 1),
                atomic(format!("array_{i}"), LessThanEqual, 3),
            ]
        })
        .collect();

    test_all_different_checker(
        premises,
        Some(atomic("array_4", GreaterThanEqual, 4)),
        Validity::Valid,
    );
}

#[test]
fn invalid_not_equal_1() {
    let premises = (1..=3)
        .flat_map(|i| {
            [
                atomic(format!("array_{i}"), GreaterThanEqual, 1),
                atomic(format!("array_{i}"), LessThanEqual, 3),
            ]
        })
        .collect();

    test_all_different_checker(
        premises,
        Some(atomic("array_4", NotEqual, 5)),
        Validity::Invalid,
    );
}

#[test]
fn invalid_conflict_detection() {
    let premises = (1..=3)
        .flat_map(|i| {
            [
                atomic(format!("array_{i}"), GreaterThanEqual, 1),
                atomic(format!("array_{i}"), LessThanEqual, 3),
            ]
        })
        .collect();

    test_all_different_checker(premises, None, Validity::Invalid);
}

fn test_all_different_checker(
    premises: Vec<Atomic>,
    propagated: Option<Atomic>,
    validity: Validity,
) {
    let mut model = Model::default();
    let variables = (1..=10)
        .map(|i| model.new_interval_variable(format!("array_{i}"), 1, 10))
        .collect();

    test_step_checker(
        model,
        |context| checking::inferences::all_different::verify(variables, context),
        premises,
        propagated,
        validity,
    );
}
