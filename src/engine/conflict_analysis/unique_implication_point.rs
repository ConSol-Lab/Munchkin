use super::ConflictAnalysisContext;
use super::ConflictResolver;
use super::LearnedNogood;
#[cfg(doc)]
use crate::engine::ConstraintSatisfactionSolver;

#[derive(Default, Debug)]
pub(crate) struct UniqueImplicationPoint {
    // TODO
}

impl ConflictResolver for UniqueImplicationPoint {
    /// Compute the 1-UIP nogood based on the current conflict.
    ///
    /// The learned nogood which is created by
    /// this method contains a single variable at the current decision level (stored at index 0
    /// of [`LearnedNogood::literals`]); the variable with the second highest
    /// decision level is stored at index 1 in [`LearnedNogood::literals`] and its
    /// decision level is (redundantly) stored in [`LearnedNogood::backjump_level`], which
    /// is used when backtracking in ([`ConstraintSatisfactionSolver`]).
    ///
    /// See the utility methods in [`ConflictAnalysisContext`] to get a better overview of which
    /// functions are available to you.
    fn resolve_conflict(
        &mut self,
        _context: &mut ConflictAnalysisContext,
    ) -> Option<LearnedNogood> {
        todo!()
    }

    fn process(
        &mut self,
        _learned_nogood: Option<LearnedNogood>,
        _context: &mut ConflictAnalysisContext,
    ) -> Result<(), ()> {
        todo!()
    }
}
