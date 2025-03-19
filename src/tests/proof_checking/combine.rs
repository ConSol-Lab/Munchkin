#![cfg(test)]

use std::num::NonZero;

use drcp_format::Comparison::*;

use crate::model::Model;
use crate::proof::checking;
use crate::proof::checking::atomic;
use crate::proof::checking::state::CheckingState;

#[test]
fn valid_combination_single_premise() {
    let mut model = Model::default();
    let _ = model.new_interval_variable("x1", 1, 5);
    let _ = model.new_interval_variable("x2", 1, 5);

    let mut state = CheckingState::from(model);

    let step_id_1 = NonZero::new(1).unwrap();
    state
        .record_inference(
            step_id_1,
            vec![atomic("x1", GreaterThanEqual, 5)],
            Some(atomic("x2", LessThanEqual, 3)),
        )
        .expect("can be recorded");

    let step_id_2 = NonZero::new(2).unwrap();
    state
        .record_inference(
            step_id_2,
            vec![atomic("x1", GreaterThanEqual, 5)],
            Some(atomic("x2", GreaterThanEqual, 4)),
        )
        .expect("can be recorded");

    checking::combine::verify(
        vec![atomic("x1", GreaterThanEqual, 5)],
        vec![step_id_1, step_id_2],
        &mut state.as_context(),
    )
    .expect("valid combine");
}

#[test]
fn valid_combination_multiple_premise() {
    let mut model = Model::default();
    let _ = model.new_interval_variable("x1", 1, 5);
    let _ = model.new_interval_variable("x2", 1, 5);
    let _ = model.new_interval_variable("x3", 1, 5);

    let mut state = CheckingState::from(model);

    let l1 = atomic("x1", GreaterThanEqual, 5);
    let l2 = atomic("x2", NotEqual, 3);
    let l3 = atomic("x3", LessThanEqual, 2);
    let l4 = atomic("x2", NotEqual, 4);

    let step_id_1 = NonZero::new(1).unwrap();
    state
        .record_inference(step_id_1, vec![l1.clone(), l2.clone()], Some(l3.clone()))
        .expect("can be recorded");

    let step_id_2 = NonZero::new(2).unwrap();
    state
        .record_inference(step_id_2, vec![l3], Some(l4.clone()))
        .expect("can be recorded");

    let step_id_3 = NonZero::new(3).unwrap();
    state
        .record_inference(step_id_3, vec![l1.clone(), l4], None)
        .expect("can be recorded");

    checking::combine::verify(
        vec![l1, l2],
        vec![step_id_1, step_id_2, step_id_3],
        &mut state.as_context(),
    )
    .expect("valid combine");
}

#[test]
fn valid_combination_including_nogood() {
    let mut model = Model::default();
    let _ = model.new_interval_variable("x1", 1, 5);
    let _ = model.new_interval_variable("x2", 1, 5);
    let _ = model.new_interval_variable("x3", 1, 5);

    let mut state = CheckingState::from(model);

    let l1 = atomic("x1", GreaterThanEqual, 5);
    let l2 = atomic("x2", NotEqual, 3);
    let l3 = atomic("x3", LessThanEqual, 2);
    let l4 = atomic("x2", NotEqual, 4);

    let step_id_1 = NonZero::new(1).unwrap();
    state
        .record_nogood(step_id_1, vec![l1.clone(), l4.clone()])
        .expect("can be recorded");

    let step_id_2 = NonZero::new(2).unwrap();
    state
        .record_inference(step_id_2, vec![l3.clone()], Some(l4.clone()))
        .expect("can be recorded");

    let step_id_3 = NonZero::new(3).unwrap();
    state
        .record_inference(step_id_3, vec![l1.clone(), l2.clone()], Some(l3.clone()))
        .expect("can be recorded");

    checking::combine::verify(
        vec![l1, l2],
        vec![step_id_1, step_id_2, step_id_3],
        &mut state.as_context(),
    )
    .expect("valid combine");
}

#[test]
fn invalid_combination_including_nogood() {
    let mut model = Model::default();
    let _ = model.new_interval_variable("x1", 1, 5);
    let _ = model.new_interval_variable("x2", 1, 5);
    let _ = model.new_interval_variable("x3", 1, 5);

    let mut state = CheckingState::from(model);

    let l1 = atomic("x1", GreaterThanEqual, 5);
    let l2 = atomic("x2", NotEqual, 3);
    let l3 = atomic("x3", LessThanEqual, 2);
    let l4 = atomic("x2", NotEqual, 4);

    let step_id_1 = NonZero::new(1).unwrap();
    state
        .record_nogood(step_id_1, vec![l1.clone(), l4.clone()])
        .expect("can be recorded");

    let step_id_2 = NonZero::new(2).unwrap();
    state
        .record_inference(step_id_2, vec![l1.clone(), l2.clone()], Some(l3.clone()))
        .expect("can be recorded");

    let _ = checking::combine::verify(
        vec![l1, l2],
        vec![step_id_1, step_id_2],
        &mut state.as_context(),
    )
    .expect_err("invalid combine");
}
