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
pub(crate) struct IHS<Var, Callback> {
    direction: OptimisationDirection,
    /// The linear objective function which is being optimised
    objective_function: Vec<Var>,
    /// The single objective variable which is optimised
    objective: Var,
    solution_callback: Callback,
}

impl<Var, Callback> IHS<Var, Callback>
where
    // The trait bound here is not common; see
    // linear_unsat_sat for more info.
    Callback: Fn(&Solver, SolutionReference),
{
    #[allow(unused, reason = "Will be used in the assignments")]
    /// Create a new instance of [`LinearSatUnsat`].
    pub(crate) fn new(
        direction: OptimisationDirection,
        objective_function: Vec<Var>,
        objective: Var,
        solution_callback: Callback,
    ) -> Self {
        Self {
            direction,
            objective_function,
            objective,
            solution_callback,
        }
    }
}

impl<Var, Callback> OptimisationProcedure<Callback> for IHS<Var, Callback>
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
        // In this method you should optimise `self.objective` according to the provided
        // `self.direction` using the Implicit Hitting Sets core-guided search approach.
        //
        // To implement this method you can use the following methods:
        // - [`Solver::lower_bound`] and/or [`Solver::upper_bound`] to retrieve the lower-bound of a
        //   variable
        // - [`Solver::satisfy`] to determine whether the current instance is feasible
        // - [`Solver::satisfy_under_assumptions`] to solve given a list of assumptions
        //   - The result of this method (a
        //     [`SatisfactionResultUnderAssumptions::UnsatisfiableUnderAssumptions`]) contains a
        //     method [`extract_core`] which allows the extraction of a core in terms of literals
        // - [`Solver::get_predicates`] which allows you to find the predicates linked to a literal.
        // - [`Solver::add_clause`] to introduce a new constraint in the form of predicates
        // - [`Solver::add_constraint`] allows you to add additional constraints
        // - [`Solver::new_bounded_integer`] allows you to create a new integer variable
        // - [`Solver::default`] allows you to create a default solver with no constraints.
        //
        // We recommend calling [`Self::update_best_solution_and_process`] when you find a
        // solution.
        todo!()
    }

    fn on_solution_callback(&self, solver: &Solver, solution: SolutionReference) {
        (self.solution_callback)(solver, solution)
    }
}
