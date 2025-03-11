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
        todo!()
    }

    fn on_solution_callback(&self, solver: &Solver, solution: SolutionReference) {
        (self.solution_callback)(solver, solution)
    }
}
