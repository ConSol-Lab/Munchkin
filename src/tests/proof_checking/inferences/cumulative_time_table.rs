#![cfg(test)]

use drcp_format::Comparison::*;

use super::test_step_checker;
use super::Validity;
use crate::model::Model;
use crate::proof::checking;
use crate::proof::checking::atomic;

#[test]
fn valid_simple_propagation() {
    let mut model = Model::default();
    let start_times = (1..=2)
        .map(|i| model.new_interval_variable(format!("task_{i}"), 1, 6))
        .collect();

    test_step_checker(
        model,
        |context| {
            checking::inferences::cumulative_time_table::verify(
                start_times,
                vec![4, 2],
                vec![1; 2],
                1,
                context,
            )
        },
        vec![
            atomic("task_1", GreaterThanEqual, 1),
            atomic("task_1", LessThanEqual, 3),
            atomic("task_2", GreaterThanEqual, 2),
            atomic("task_2", LessThanEqual, 5),
        ],
        Some(atomic("task_2", GreaterThanEqual, 5)),
        Validity::Valid,
    );
}

#[test]
fn invalid_simple_propagation() {
    let mut model = Model::default();
    let start_times = (1..=2)
        .map(|i| model.new_interval_variable(format!("task_{i}"), 1, 6))
        .collect();

    test_step_checker(
        model,
        |context| {
            checking::inferences::cumulative_time_table::verify(
                start_times,
                vec![4, 2],
                vec![1; 2],
                1,
                context,
            )
        },
        vec![
            atomic("task_1", GreaterThanEqual, 1),
            atomic("task_1", LessThanEqual, 3),
            atomic("task_2", LessThanEqual, 5),
        ],
        Some(atomic("task_2", GreaterThanEqual, 5)),
        Validity::Invalid,
    );
}
