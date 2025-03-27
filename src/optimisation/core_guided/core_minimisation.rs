use crate::branching::Brancher;
use crate::predicates::Predicate;
use crate::termination::TerminationCondition;
use crate::Solver;

pub(crate) struct CoreMinimiser;

impl CoreMinimiser {
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
        // You can use the provided `termination` and `brancher`. If you would like to use a
        // smaller time limit then that is also possible using [`TimeBudget::starting_now`] or you
        // can impose a conflict limit using [`ConflictBudget::with_budget`] (or a combination of
        // the two using [`Combinator::new`]).
        todo!();

        // We add the statistic of how many elements were removed by core minimisation
        solver
            .get_minimisation_statistics()
            .add_term((core.len() - num_elements_before) as u64);
    }
}
