#![cfg(test)]

use drcp_format::Comparison::*;

use super::test_step_checker;
use super::Validity;
use crate::model::Model;
use crate::proof::checking;
use crate::proof::checking::atomic;
use crate::proof::checking::Atomic;

#[test]
fn valid_prevent_closing() {
    test_circuit_checker(
        vec![atomic("array_1", Equal, 2), atomic("array_2", Equal, 3)],
        Some(atomic("array_3", NotEqual, 1)),
        Validity::Valid,
    );
}

#[test]
fn invalid_prevent_closing() {
    test_circuit_checker(
        vec![atomic("array_1", Equal, 2), atomic("array_2", Equal, 3)],
        Some(atomic("array_3", NotEqual, 4)),
        Validity::Invalid,
    );
}

#[test]
fn valid_check_of_sub_circuit() {
    test_circuit_checker(
        vec![atomic("array_3", Equal, 2), atomic("array_2", Equal, 3)],
        None,
        Validity::Valid,
    );
}

#[test]
fn invalid_sub_circuit_detection() {
    test_circuit_checker(
        vec![],
        Some(atomic("array_3", NotEqual, 4)),
        Validity::Invalid,
    );
}

#[test]
fn invalid_sub_circuit_detection_2() {
    test_circuit_checker(
        vec![atomic("array_3", Equal, 2), atomic("array_2", Equal, 3)],
        None,
        Validity::Invalid,
    );
}

#[test]
fn valid_strongly_connected_components_are_identified() {
    test_circuit_checker(
        vec![
            atomic("array_3", NotEqual, 1),
            atomic("array_3", NotEqual, 2),
            atomic("array_4", NotEqual, 1),
            atomic("array_4", NotEqual, 2),
        ],
        Some(atomic("array_5", NotEqual, 3)),
        Validity::Valid,
    );
}

#[test]
fn invalid_strongly_components_are_identified() {
    test_circuit_checker(
        vec![
            atomic("array_3", NotEqual, 1),
            atomic("array_4", NotEqual, 1),
            atomic("array_4", NotEqual, 2),
        ],
        Some(atomic("array_5", NotEqual, 3)),
        Validity::Invalid,
    );
}

fn test_circuit_checker(premises: Vec<Atomic>, propagated: Option<Atomic>, validity: Validity) {
    let mut model = Model::default();
    let variables = (1..=5)
        .map(|i| model.new_interval_variable(format!("array_{i}"), 1, 5))
        .collect();

    test_step_checker(
        model,
        |context| checking::inferences::circuit_prevent_and_check::verify(variables, context),
        premises,
        propagated,
        validity,
    );
}
