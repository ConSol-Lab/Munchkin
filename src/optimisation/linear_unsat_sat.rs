use super::OptimisationProcedure;
use crate::branching::Brancher;
use crate::results::OptimisationResult;
use crate::results::SolutionReference;
use crate::solver::OptimisationDirection;
use crate::termination::TerminationCondition;
use crate::variables::IntegerVariable;
use crate::Solver;

/// Implements the linear UNSAT-SAT (LUS) optimisation procedure.
#[derive(Debug, Clone, Copy)]
#[allow(unused, reason = "Will be used in the assignment")]
pub struct LinearUnsatSat<Var, Callback> {
    direction: OptimisationDirection,
    objective: Var,
    solution_callback: Callback,
}

impl<Var, Callback> LinearUnsatSat<Var, Callback>
where
    // The trait bound here is not common; see
    // linear_unsat_sat for more info.
    Callback: Fn(&Solver, SolutionReference),
{
    /// Create a new instance of [`LinearSatUnsat`].
    pub fn new(
        direction: OptimisationDirection,
        objective: Var,
        solution_callback: Callback,
    ) -> Self {
        Self {
            direction,
            objective,
            solution_callback,
        }
    }
}

impl<Var, Callback> OptimisationProcedure<Callback> for LinearUnsatSat<Var, Callback>
where
    Var: IntegerVariable,
    Callback: Fn(&Solver, SolutionReference),
{
    fn optimise(
        &mut self,
        _brancher: &mut impl Brancher,
        _termination: &mut impl TerminationCondition,
        _solver: &mut Solver,
    ) -> OptimisationResult {
        // In this method you should optimise `self.objective`; you can ignore the direction as it
        // will always be minimising.
        //
        // IMPORTANT NOTE: Always ensure that you check the provided [`TerminationCondition`] using
        // [`TerminationCondition::should_stop`] and return a [`OptimisationResult::Unknown`] if
        // this method returns true.
        //
        // To implement this method you can use the following methods:
        // - [`Solver::lower_bound`] and/or [`Solver::upper_bound`] to retrieve the lower-bound of
        // a variable
        // - [`Solver::satisfy`] to determine whether the current instance is feasible
        // - [`Solver::satisfy_under_assumptions`] to solve given a list of assumptions
        // - [`Solver::add_clause`] to introduce a new constraint in the form of predicates
        //
        // We recommend calling [`Self::update_best_solution_and_process`] when you find a
        // solution.
        todo!()
    }

    fn on_solution_callback(&self, solver: &Solver, solution: SolutionReference) {
        (self.solution_callback)(solver, solution)
    }
}
