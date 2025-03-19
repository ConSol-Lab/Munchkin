#![cfg(test)]

use drcp_format::Comparison::*;

use super::test_step_checker;
use super::Validity;
use crate::model::Model;
use crate::proof::checking;
use crate::proof::checking::atomic;
use crate::proof::checking::Atomic;

#[test]
fn valid_lower_bound_of_rhs() {
    test_maximum_checker(
        vec![atomic("array_1", GreaterThanEqual, 6)],
        atomic("rhs", GreaterThanEqual, 6),
        Validity::Valid,
    );
}

#[test]
fn valid_lower_bound_of_rhs_poor() {
    test_maximum_checker(
        vec![
            atomic("array_1", GreaterThanEqual, 6),
            atomic("array_2", GreaterThanEqual, 7),
        ],
        atomic("rhs", GreaterThanEqual, 6),
        Validity::Valid,
    );
}

#[test]
fn invalid_upper_bound_of_rhs() {
    test_maximum_checker(
        vec![
            atomic("array_1", LessThanEqual, 6),
            atomic("array_2", LessThanEqual, 7),
        ],
        atomic("rhs", LessThanEqual, 6),
        Validity::Invalid,
    );
}

#[test]
fn invalid_lower_bound_of_rhs() {
    test_maximum_checker(
        vec![
            atomic("array_1", GreaterThanEqual, 6),
            atomic("array_2", GreaterThanEqual, 7),
        ],
        atomic("rhs", GreaterThanEqual, 8),
        Validity::Invalid,
    );
}

#[test]
fn valid_upper_bound_of_rhs() {
    test_maximum_checker(
        vec![
            atomic("array_1", LessThanEqual, 6),
            atomic("array_2", LessThanEqual, 6),
            atomic("array_3", LessThanEqual, 6),
            atomic("array_4", LessThanEqual, 6),
        ],
        atomic("rhs", LessThanEqual, 6),
        Validity::Valid,
    );
}

fn test_maximum_checker(premises: Vec<Atomic>, propagated: Atomic, validity: Validity) {
    let mut model = Model::default();

    let terms = (1..=4)
        .map(|i| model.new_interval_variable(format!("array_{i}"), 1, 10))
        .collect();
    let rhs = model.new_interval_variable("rhs", 0, 20);

    test_step_checker(
        model,
        |context| checking::inferences::maximum::verify(terms, rhs, context),
        premises,
        Some(propagated),
        validity,
    );
}
