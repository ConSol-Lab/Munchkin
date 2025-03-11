use crate::branching::Brancher;
use crate::optimisation::OptimisationProcedure;
use crate::results::OptimisationResult;
use crate::results::SolutionReference;
use crate::solver::OptimisationDirection;
use crate::termination::TerminationCondition;
use crate::variables::IntegerVariable;
use crate::Solver;

/// Implements the core-guided search optimisation procedure.
#[derive(Debug, Clone)]
#[allow(unused, reason = "Will be used in the assignments")]
pub(crate) struct CoreGuidedSearch<Var, Callback> {
    direction: OptimisationDirection,
    objective: Vec<Var>,
    solution_callback: Callback,
}

impl<Var, Callback> CoreGuidedSearch<Var, Callback>
where
    // The trait bound here is not common; see
    // linear_unsat_sat for more info.
    Callback: Fn(&Solver, SolutionReference),
{
    #[allow(unused, reason = "Will be used in the assignments")]
    /// Create a new instance of [`LinearSatUnsat`].
    pub(crate) fn new(
        direction: OptimisationDirection,
        objective: Vec<Var>,
        solution_callback: Callback,
    ) -> Self {
        Self {
            direction,
            objective,
            solution_callback,
        }
    }
}

impl<Var, Callback> OptimisationProcedure<Callback> for CoreGuidedSearch<Var, Callback>
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
