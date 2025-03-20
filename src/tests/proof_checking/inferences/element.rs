#![cfg(test)]

//! All tests are run on the following model:
//! ```mzn
//! array [1..4] of var 4..10: Array;
//! var 0..10: Index;
//! var 0..20: Value;
//! constraint element(Array, Index, Value);
//! ```

use drcp_format::Comparison::*;

use super::test_step_checker;
use super::Validity;
use crate::model::Model;
use crate::proof::checking;
use crate::proof::checking::atomic;
use crate::proof::checking::Atomic;

#[test]
fn valid_rhs_upper_bound_based_on_upper_bounds_of_array_elements() {
    test_element_checker(
        vec![
            atomic("array_3", LessThanEqual, 8),
            atomic("array_4", LessThanEqual, 7),
            atomic("array_2", LessThanEqual, 6),
            atomic("array_1", LessThanEqual, 5),
        ],
        atomic("rhs", LessThanEqual, 8),
        Validity::Valid,
    )
}

#[test]
fn invalid_rhs_bounds_conclusion() {
    test_element_checker(
        vec![
            atomic("array_3", LessThanEqual, 5),
            atomic("array_2", LessThanEqual, 5),
            atomic("array_1", LessThanEqual, 5),
        ],
        atomic("rhs", LessThanEqual, 5),
        Validity::Invalid,
    )
}

#[test]
fn valid_rhs_lower_bound_based_on_lower_bounds_of_array_elements() {
    test_element_checker(
        vec![
            atomic("array_3", GreaterThanEqual, 9),
            atomic("array_4", GreaterThanEqual, 8),
            atomic("array_2", GreaterThanEqual, 7),
            atomic("array_1", GreaterThanEqual, 6),
        ],
        atomic("rhs", GreaterThanEqual, 6),
        Validity::Valid,
    )
}

#[test]
fn valid_rhs_bound_if_index_is_constrained() {
    test_element_checker(
        vec![
            atomic("index", GreaterThanEqual, 2),
            atomic("index", LessThanEqual, 5),
            atomic("array_2", LessThanEqual, 5),
            atomic("array_3", LessThanEqual, 5),
        ],
        atomic("rhs", LessThanEqual, 5),
        Validity::Valid,
    )
}

#[test]
fn valid_index_lower_bound_is_propagated() {
    test_element_checker(
        vec![],
        atomic("index", GreaterThanEqual, 1),
        Validity::Valid,
    )
}

#[test]
fn valid_index_upper_bound_is_propagated() {
    test_element_checker(vec![], atomic("index", LessThanEqual, 4), Validity::Valid)
}

#[test]
fn invalid_array_element_is_mutated() {
    test_element_checker(
        vec![atomic("rhs", LessThanEqual, 4)],
        atomic("array_1", LessThanEqual, 4),
        Validity::Invalid,
    )
}

fn test_element_checker(premises: Vec<Atomic>, propagated: Atomic, validity: Validity) {
    let mut model = Model::default();

    let array = (1..=4)
        .map(|i| model.new_interval_variable(format!("array_{i}"), 4, 10))
        .collect();
    let index = model.new_interval_variable("index", 0, 10);
    let rhs = model.new_interval_variable("rhs", 0, 20);

    test_step_checker(
        model,
        |context| checking::inferences::element::verify(array, index, rhs, context),
        premises,
        Some(propagated),
        validity,
    );
}
