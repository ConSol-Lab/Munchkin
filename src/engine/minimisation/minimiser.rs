use super::MinimisationContext;
use crate::engine::conflict_analysis::LearnedNogood;
use crate::engine::cp::propagation::PropagationContext;

/// A trait which determines the behaviour of minimisers
pub(crate) trait Minimiser: Default {
    /// Takes as input a [`LearnedNogood`] and minimises the nogood based on some strategy.
    fn minimise(&mut self, context: MinimisationContext, learned_nogood: &mut LearnedNogood);
}

/// Recomputes the invariants of the [`LearnedNogood`].
pub(crate) fn recompute_invariants(
    _context: PropagationContext,
    _learned_nogood: &mut LearnedNogood,
) {
    todo!()
}
