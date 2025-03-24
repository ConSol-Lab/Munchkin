use crate::predicates::Predicate;
use crate::Solver;

pub(super) struct CoreMinimiser;

impl CoreMinimiser {
    /// Minimises the provided `core` using deletion-based core minimisation
    #[allow(unused, reason = "Will be used in the assignment")]
    #[allow(clippy::ptr_arg, reason = "Will not be present when implemented")]
    pub(super) fn minimise_core(_core: &mut Vec<Predicate>, _solver: &mut Solver) {
        // In this method you should minimise `core` using deletion-based core minimisation.
        //
        // To implement this method you can use the following methods:
        // - [`Solver::satisfy_under_assumptions`] to solve given a list of assumptions
        todo!()
    }
}
