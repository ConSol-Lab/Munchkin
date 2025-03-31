#![cfg(test)]
use std::num::NonZero;

use crate::branching::branchers::independent_variable_value_brancher::IndependentVariableValueBrancher;
use crate::branching::InDomainMax;
use crate::branching::InputOrder;
use crate::constraints;
use crate::constraints::NegatableConstraint;
use crate::optimisation::ImplicitHittingSets;
use crate::optimisation::OptimisationProcedure;
use crate::results::OptimisationResult;
use crate::results::ProblemSolution;
use crate::results::SolutionReference;
use crate::termination::Indefinite;
use crate::variables::TransformableVariable;
use crate::Solver;

#[test]
fn simple_optimisation_problem() {
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

    let o = solver.new_bounded_integer(0, 4);
    let result = solver
        .add_constraint(constraints::equals(
            [
                x.scaled(1),
                y.scaled(1),
                z.scaled(1),
                a.scaled(1),
                o.scaled(-1),
            ],
            0,
        ))
        .post(NonZero::new(1).unwrap());
    assert!(result.is_ok());

    let empty_callback: fn(&Solver, SolutionReference) = |_, _| {};

    let mut ihs = ImplicitHittingSets::new(
        crate::solver::OptimisationDirection::Minimise,
        vec![x, y, z, a],
        o,
        empty_callback,
        false,
    );
    let result = ihs.optimise(
        &mut IndependentVariableValueBrancher::new(
            InputOrder::new(vec![x, y, z, a, o]),
            InDomainMax,
        ),
        &mut Indefinite,
        &mut solver,
    );

    match result {
        OptimisationResult::Optimal(solution) => {
            let x_value = solution.get_integer_value(x);
            let y_value = solution.get_integer_value(y);
            let z_value = solution.get_integer_value(z);
            let a_value = solution.get_integer_value(a);
            let o_value = solution.get_integer_value(o);

            assert!(x_value + y_value + a_value >= 2);
            assert!(z_value + a_value <= 1);
            assert_eq!(o_value, 2);
        }
        result => {
            panic!("Should have been optimal but was {result:?}")
        }
    }
}
