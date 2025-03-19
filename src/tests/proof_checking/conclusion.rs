#![cfg(test)]

use std::num::NonZero;

use drcp_format::Comparison::*;

use crate::model::Model;
use crate::proof::checking;
use crate::proof::checking::atomic;
use crate::proof::checking::state::CheckingState;

#[test]
fn valid_unsat_conclusion() {
    let model = Model::default();
    let mut state = CheckingState::from(model);

    let step_id_1 = NonZero::new(1).unwrap();
    state
        .record_nogood(step_id_1, vec![])
        .expect("can be recorded");

    checking::conclusion::verify_unsat(state).expect("valid unsat conclusion");
}

#[test]
fn invalid_unsat_conclusion() {
    let model = Model::default();
    let state = CheckingState::from(model);

    let _ = checking::conclusion::verify_unsat(state).expect_err("invalid combine");
}

#[test]
fn valid_optimal_conclusion() {
    let mut model = Model::default();
    let _ = model.new_interval_variable("x", 4, 4);

    let state = CheckingState::from(model);

    checking::conclusion::verify_optimal(state, atomic("x", GreaterThanEqual, 4))
        .expect("valid optimal conclusion");
}

#[test]
fn valid_optimal_conclusion_2() {
    let mut model = Model::default();
    let _ = model.new_interval_variable("x", 4, 4);

    let state = CheckingState::from(model);

    checking::conclusion::verify_optimal(state, atomic("x", LessThanEqual, 4))
        .expect("valid optimal conclusion");
}

#[test]
fn invalid_optimal_conclusion() {
    let mut model = Model::default();
    let _ = model.new_interval_variable("x", 4, 6);

    let state = CheckingState::from(model);

    let _ = checking::conclusion::verify_optimal(state, atomic("x", GreaterThanEqual, 5))
        .expect_err("invalid optimal conclusion");
}
