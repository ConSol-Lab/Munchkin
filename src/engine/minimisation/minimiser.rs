use super::MinimisationContext;
use crate::engine::conflict_analysis::LearnedNogood;
use crate::engine::cp::propagation::propagation_context::HasAssignments;
use crate::engine::cp::propagation::ReadDomains;

/// A trait which determines the behaviour of minimisers
pub(crate) trait Minimiser: Default {
    /// Takes as input a [`LearnedNogood`] and minimises the nogood based on some strategy.
    fn minimise(&mut self, context: MinimisationContext, learned_nogood: &mut LearnedNogood);
}

/// Recomputes the invariants of the [`LearnedNogood`].
///
/// i.e. puts the literal of the current decision level at the `0`-th position and a literal from
/// the backjump level at the `1`-st position.
pub(crate) fn recompute_invariants<Context: HasAssignments + ReadDomains>(
    _context: &Context,
    _learned_nogood: &mut LearnedNogood,
) {
    todo!("Implement this helper function to recompute the invariants of 'LearnedNogood'")
}
