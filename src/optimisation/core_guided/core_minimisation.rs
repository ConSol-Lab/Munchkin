use std::time::Duration;

use crate::branching::Brancher;
use crate::predicates::Predicate;
use crate::termination::Combinator;
use crate::termination::ConflictBudget;
use crate::termination::TerminationCondition;
use crate::termination::TimeBudget;
use crate::Solver;

pub(crate) struct CoreMinimiser;

impl CoreMinimiser {
    /// Creates a new termination condition consisting of the original timing budget, a new budget
    /// with 500 milliseconds, and a new conflict budget using the provided `budget`.
    pub(crate) fn create_termination_condition(
        original_termination_budget: &mut impl TerminationCondition,
        budget: usize,
    ) -> impl TerminationCondition {
        Combinator::new(
            Combinator::new(
                original_termination_budget.clone(),
                TimeBudget::starting_now(Duration::from_millis(500)),
            ),
            ConflictBudget::with_budget(budget),
        )
    }
    /// Minimises the provided `core` using deletion-based core minimisation
    #[allow(unused, reason = "Will be used in the assignment")]
    #[allow(clippy::ptr_arg, reason = "Will not be present when implemented")]
    pub(crate) fn minimise_core(
        core: &mut Vec<Predicate>,
        solver: &mut Solver,
        termination: &mut impl TerminationCondition,
        brancher: &mut impl Brancher,
    ) {
        let num_elements_before = core.len();
        // In this method you should minimise `core` using deletion-based core minimisation.
        //
        // To implement this method you can use the following methods:
        // - [`Solver::satisfy_under_assumptions`] to solve given a list of assumptions
        //
        // Use the provided `termination_condition` as input; you should change the conflict
        // budget.
        let conflict_budget = todo!();
        let mut termination_condition =
            Self::create_termination_condition(termination, conflict_budget);

        todo!();

        // We add the statistic of how many elements were removed by core minimisation
        solver
            .get_minimisation_statistics()
            .add_term((core.len() - num_elements_before) as u64);
    }
}
