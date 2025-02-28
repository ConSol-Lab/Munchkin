use super::PropagatorInitialisationContext;
#[cfg(doc)]
use crate::asserts::ASSERT_ADVANCED;
#[cfg(doc)]
use crate::asserts::ASSERT_EXTREME;
#[cfg(doc)]
use crate::basic_types::Inconsistency;
use crate::basic_types::PropagationStatusCP;
use crate::engine::cp::propagation::propagation_context::PropagationContext;
use crate::engine::cp::propagation::propagation_context::PropagationContextMut;
#[cfg(doc)]
use crate::engine::sat::ClausalPropagator;
#[cfg(doc)]
use crate::engine::ConstraintSatisfactionSolver;
use crate::predicates::PropositionalConjunction;

/// All propagators implement the [`Propagator`] trait, with the exception of the
/// clausal propagator. Structs implementing the trait defines the main propagator logic with
/// regards to propagation, detecting conflicts, and providing explanations.
///
/// The only required functions are [`Propagator::debug_propagate_from_scratch`] and
/// [`Propagator::name`], all other functions have default implementations. For initial development,
/// the required functions are enough, but a more mature implementation consider all functions in
/// most cases.
///
/// See the [`crate::engine::cp::propagation`] documentation for more details.
pub trait Propagator {
    /// Return the name of the propagator, this is a convenience method that is used for printing.
    fn name(&self) -> &str;

    /// Propagate method that will be called during search (e.g. in
    /// [`ConstraintSatisfactionSolver::solve`]).
    ///
    /// This method extends the current partial
    /// assignments with inferred domain changes found by the
    /// [`Propagator`]. In case no conflict has been detected it should return
    /// [`Result::Ok`], otherwise it should return a [`Result::Err`] with an [`Inconsistency`] which
    /// contains the reason for the failure; either because a propagation caused an
    /// an empty domain ([`Inconsistency::EmptyDomain`]) or because the logic of the propagator
    /// found the current state to be inconsistent ([`Inconsistency::Other`]).
    ///
    /// Note that the failure (explanation) is given as a conjunction of predicates that lead to the
    /// failure
    ///
    /// Propagators are not required to propagate until a fixed point. It will be called
    /// again by the solver until no further propagations happen.
    ///
    /// By default, this function calls [`Propagator::debug_propagate_from_scratch`].
    fn propagate(&self, context: PropagationContextMut) -> PropagationStatusCP;

    /// Initialises the propagator without performing propagation. This method is called only once
    /// by the [`ConstraintSatisfactionSolver`] when the propagator is added using
    /// [`ConstraintSatisfactionSolver::add_propagator`].
    ///
    /// The method can be used to detect root-level inconsistencies and to register variables used
    /// for notifications (see [`Propagator::notify`]) by calling
    /// [`PropagatorInitialisationContext::register`].
    ///
    /// The solver will call this before any call to [`Propagator::propagate`] is made.
    fn initialise_at_root(
        &mut self,
        _: &mut PropagatorInitialisationContext,
    ) -> Result<(), PropositionalConjunction>;

    /// A check whether this propagator can detect an inconsistency.
    ///
    /// By implementing this function, if the propagator is reified, it can propagate the
    /// reification literal based on the detected inconsistency. Yet, an implementation is not
    /// needed for correctness, as [`Propagator::propagate`] should still check for
    /// inconsistency as well.
    fn detect_inconsistency(
        &self,
        _context: PropagationContext,
    ) -> Option<PropositionalConjunction> {
        None
    }
}
