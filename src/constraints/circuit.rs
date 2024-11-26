use super::Constraint;
use crate::propagators::circuit::CircuitPropagator;
use crate::variables::IntegerVariable;

/// Creates the [`Constraint`] that enforces that the assigned successors form a circuit
/// (i.e. a path which visits each vertex once and starts and ends at the same node).
///
/// `successor[i] = j` means that `j` is the successor of `i`.
pub fn circuit<Var: IntegerVariable + 'static>(
    successor: impl Into<Box<[Var]>>,
) -> impl Constraint {
    CircuitPropagator::new(successor.into())
}
