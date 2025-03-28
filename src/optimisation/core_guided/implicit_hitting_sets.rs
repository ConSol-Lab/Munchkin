use std::num::NonZero;

use crate::branching::branchers::independent_variable_value_brancher::IndependentVariableValueBrancher;
use crate::branching::Brancher;
use crate::branching::ValueSelector;
use crate::branching::VariableSelector;
use crate::constraints;
use crate::munchkin_assert_simple;
use crate::optimisation::LinearUnsatSat;
use crate::optimisation::OptimisationProcedure;
use crate::results::OptimisationResult;
use crate::results::SolutionReference;
use crate::solver::OptimisationDirection;
use crate::termination::TerminationCondition;
use crate::variables::DomainId;
use crate::variables::IntegerVariable;
use crate::variables::TransformableVariable;
use crate::Solver;

/// Implements the core-guided search optimisation procedure.
#[derive(Debug, Clone)]
#[allow(unused, reason = "Will be used in the assignments")]
pub(crate) struct ImplicitHittingSets<Callback> {
    direction: OptimisationDirection,
    /// The linear objective function which is being optimised
    objective_function: Vec<DomainId>,
    /// The single objective variable which is optimised
    objective: DomainId,
    solution_callback: Callback,
    /// Whether to use core minimisation
    use_core_minimisation: bool,
}

impl<Callback> ImplicitHittingSets<Callback>
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
        use_core_minimisation: bool,
    ) -> Self {
        Self {
            direction,
            objective_function,
            objective,
            solution_callback,
            use_core_minimisation,
        }
    }

    /// Creates a place-holder empty function which does not do anything when a solution is found.
    fn create_empty_function() -> impl Fn(&Solver, SolutionReference) {
        |_, _| {}
    }
    /// Given the provided [`VariableSelector`] and [`ValueSelector`]; it creates a new
    /// [`Brancher`].
    #[allow(unused, reason = "Will be used in the assignments")]
    fn create_search<
        Var: IntegerVariable,
        VarSelection: VariableSelector<Var>,
        ValSelection: ValueSelector<Var>,
    >(
        variable_selection: VarSelection,
        value_selection: ValSelection,
    ) -> impl Brancher {
        IndependentVariableValueBrancher::new(variable_selection, value_selection)
    }

    /// Given the [`Solver`] and `objective_variables`, it creates a new [`OptimisationProcedure`]
    /// which minimises the sum of the provided objective variables.
    ///
    /// Side note: this function will add an additional constraint to the solver which should not
    /// impact the feasibility of the solver!
    #[allow(unused, reason = "Will be used in the assignments")]
    fn create_optimisation_procedure(
        solver: &mut Solver,
        objective_variables: &[DomainId],
    ) -> LinearUnsatSat<DomainId, impl Fn(&Solver, SolutionReference<'_>)> {
        munchkin_assert_simple!(
            !objective_variables.is_empty(),
            "Provided objective variables should not be empty"
        );

        let lb = objective_variables
            .iter()
            .map(|var| solver.lower_bound(var))
            .min()
            .unwrap();
        let ub = objective_variables
            .iter()
            .map(|var| solver.upper_bound(var))
            .max()
            .unwrap();

        let objective_variable = solver.new_bounded_integer(lb, ub);

        let result = solver
            .add_constraint(constraints::equals(
                objective_variables
                    .iter()
                    .map(|&variable| variable.scaled(1))
                    .chain(std::iter::once(objective_variable.scaled(-1)))
                    .collect::<Vec<_>>(),
                0,
            ))
            .post(NonZero::new(1).unwrap());

        munchkin_assert_simple!(
            result.is_ok(),
            "Adding constraint over objective variables should never lead to unsatisfiability"
        );

        LinearUnsatSat::new(
            OptimisationDirection::Minimise,
            objective_variable,
            Self::create_empty_function(),
        )
    }
}

impl<Callback> OptimisationProcedure<Callback> for ImplicitHittingSets<Callback>
where
    Callback: Fn(&Solver, SolutionReference),
{
    fn optimise(
        &mut self,
        _brancher: &mut impl Brancher,
        _termination: &mut impl TerminationCondition,
        solver: &mut Solver,
    ) -> OptimisationResult {
        // In this method you should optimise `self.objective`; you can ignore the direction as it
        // will always be minimising.
        //
        // IMPORTANT NOTE: Always ensure that you check the provided [`TerminationCondition`] using
        // [`TerminationCondition::should_stop`] and return a [`OptimisationResult::Unknown`] if
        // this method returns true.
        //
        // To implement this method you can use the following methods:
        // - [`Solver::lower_bound`] and/or [`Solver::upper_bound`] to retrieve the lower-bound of a
        //   variable
        // - [`Solver::satisfy`] to determine whether the current instance is feasible
        // - [`Solver::satisfy_under_assumptions`] to solve given a list of assumptions
        //   - The result of this method (a
        //     [`SatisfactionResultUnderAssumptions::UnsatisfiableUnderAssumptions`]) contains a
        //     method [`extract_core`] which allows the extraction of a core in terms of predicates
        // - [`Solver::add_constraint`] allows you to add additional constraints; for example, if
        //   you want to add a the constraint that the sum of a set of variables `x` should be less
        //   than or equal to `c` then you can do this using
        //   `solver.add_constraint(constraints::less_than_or_equals(x,
        //   c)).post(NonZero::new(1).unwrap())`
        // - [`Solver::new_bounded_integer`] allows you to create a new integer variable
        //
        // As the main solver you can make use of the `main_solver` defined below which has been
        // created to contain no constraints and the same variables as the `solver` provided to this
        // method. You can add nogoods using the method [`Solver::add_nogood`].
        //
        // You can then optimise using the function [`Solver::optimise`] which takes
        // three inputs:
        // 1. A [`Brancher`] which you should create using [`Self::create_search`] which you would
        //    provide with a variable and value selector. For example, if you have a list of
        //    variables `x` then you would use the function as follows:
        //    `Self::create_search(InputOrder::new(x), InDomainMin)`. You should be able to provide
        //    it with the same `brancher` passed to this method.
        // 2. A [`TerminationCondition`] - Use the same [`TerminationCondition`] as passed to this
        //    method.
        // 3. An [`OptimisationProcedure`] - You can use the function
        //    [`Self::create_optimisation_procedure`] which minimises the sum of a set of integer
        //    variables using the Linear UNSAT-SAT approach
        //
        // We recommend calling [`Self::update_best_solution_and_process`] when you find a
        // solution.
        //
        // The variable `self.use_core_minimisation` indicates whether or not the optimisation
        // procedure should use core minimisation. Core minimisation can be called using
        // [`CoreMinimiser::minimise_core`].

        #[allow(
            unused_variables,
            unused_mut,
            reason = "Will be used in the assignment"
        )]
        let mut main_solver = solver.create_empty_clone();

        todo!()
    }

    fn on_solution_callback(&self, solver: &Solver, solution: SolutionReference) {
        (self.solution_callback)(solver, solution)
    }
}
