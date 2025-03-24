#![cfg(test)]
use std::num::NonZero;

use crate::constraints;
use crate::constraints::NegatableConstraint;
use crate::optimisation::core_minimisation::CoreMinimiser;
use crate::predicate;
use crate::Solver;

#[test]
fn simple_core_minimisation() {
    let mut solver = Solver::default();
    let x = solver.new_bounded_integer(0, 1);
    let y = solver.new_bounded_integer(0, 1);
    let z = solver.new_bounded_integer(0, 1);
    let a = solver.new_bounded_integer(0, 1);

    // x + y + a >= 2
    let result = solver
        .add_constraint(constraints::less_than_or_equals([x, y, a], 1).negation())
        .post(NonZero::new(1).unwrap());
    assert!(result.is_ok());

    // z + a <= 1
    let result = solver
        .add_constraint(constraints::less_than_or_equals([z, a], 1))
        .post(NonZero::new(1).unwrap());
    assert!(result.is_ok());

    let mut core = vec![
        predicate!(x <= 0),
        predicate!(y <= 0),
        predicate!(z <= 0),
        predicate!(a <= 0),
    ];
    CoreMinimiser::minimise_core(&mut core, &mut solver);
    assert_eq!(vec![predicate!(x <= 0), predicate!(y <= 0)], core);
}
