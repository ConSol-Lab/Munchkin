use std::num::NonZero;

use crate::branching::Brancher;
use crate::constraints;
use crate::munchkin_assert_simple;
use crate::optimisation::OptimisationProcedure;
use crate::results::OptimisationResult;
use crate::results::SolutionReference;
use crate::solver::OptimisationDirection;
use crate::termination::TerminationCondition;
use crate::variables::DomainId;
use crate::variables::TransformableVariable;
use crate::Solver;

/// Implements the core-guided search optimisation procedure.
#[derive(Debug, Clone)]
#[allow(unused, reason = "Will be used in the assignments")]
pub(crate) struct Oll<Callback> {
    direction: OptimisationDirection,
    /// The linear objective function which is being optimised
    objective_function: Vec<DomainId>,
    /// The single objective variable which is optimised
    objective: DomainId,
    solution_callback: Callback,
}

impl<Callback> Oll<Callback>
where
    // The trait bound here is not common; see
    // linear_unsat_sat for more info.
    Callback: Fn(&Solver, SolutionReference),
{
    #[allow(unused, reason = "Will be used in the assignments")]
    /// Create a new instance of [`LinearSatUnsat`].
    pub(crate) fn new(
        direction: OptimisationDirection,
        objective_function: Vec<DomainId>,
        objective: DomainId,
        solution_callback: Callback,
    ) -> Self {
        Self {
            direction,
            objective_function,
            objective,
            solution_callback,
        }
    }

    /// Adds a constraint to the solver that `\sum variables <= new_var`
    #[allow(unused, reason = "Will be used in the assignments")]
    pub(crate) fn create_linear_inequality(
        solver: &mut Solver,
        variables: &[DomainId],
        new_var: DomainId,
    ) {
        let result = solver
            .add_constraint(constraints::less_than_or_equals(
                variables
                    .iter()
                    .map(|&var| var.scaled(1))
                    .chain(std::iter::once(new_var.scaled(-1)))
                    .collect::<Vec<_>>(),
                0,
            ))
            .post(NonZero::new(1).unwrap());
        munchkin_assert_simple!(
            result.is_ok(),
            "Adding new constraint over objective variables should not result in error"
        );
    }
}

impl<Callback> OptimisationProcedure<Callback> for Oll<Callback>
where
    Callback: Fn(&Solver, SolutionReference),
{
    fn optimise(
        &mut self,
        _brancher: &mut impl Brancher,
        _termination: &mut impl TerminationCondition,
        _solver: &mut Solver,
    ) -> OptimisationResult {
        // In this method you should optimise `self.objective` according to the provided
        // `self.direction` using the OLL core-guided search approach.
        //
        // To implement this method you can use the following methods:
        // - [`Solver::lower_bound`] and/or [`Solver::upper_bound`] to retrieve the lower-bound of a
        //   variable
        // - [`Solver::satisfy`] to determine whether the current instance is feasible
        // - [`Solver::satisfy_under_assumptions`] to solve given a list of assumptions
        //   - The result of this method (a
        //     [`SatisfactionResultUnderAssumptions::UnsatisfiableUnderAssumptions`]) contains a
        //     method [`extract_core`] which allows the extraction of a core in terms of literals
        // - [`Solver::add_constraint`] allows you to add additional constraints; for example, if
        //   you want to add a the constraint that the sum of a set of variables `x` should be less
        //   than or equal to `c` then you can do this using
        //   `solver.add_constraint(constraints::less_than_or_equals(x,
        //   c)).post(NonZero::new(1).unwrap())`
        // - [`Solver::new_bounded_integer`] allows you to create a new integer variable a predicate
        //   such that it can be used in linear sums.
        //
        // To create a constraint of the form `\sum x <= d` where `d` is a variable, you can use the
        // function [`Self::create_linear_inequality`].
        //
        // We recommend calling [`Self::update_best_solution_and_process`] when you find a
        // solution.
        todo!()
    }

    fn on_solution_callback(&self, solver: &Solver, solution: SolutionReference) {
        (self.solution_callback)(solver, solution)
    }
}
