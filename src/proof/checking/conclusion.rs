use super::state::CheckingState;
use super::Atomic;

/// Verify that the conclusion that the model is unsatisfiable is valid. If we cannot conclude
/// unsatisfiability yet, an error is returned.
#[allow(unused_variables, reason = "to be implemented by students")]
pub(crate) fn verify_unsat(state: CheckingState) -> anyhow::Result<()> {
    // The state will have accumulated nogoods from all the combine steps encountered in the proof.
    // If one of the nogoods is `true -> false`, then the state will be inconsistent. This can be
    // tested with [`CheckingState::is_inconsistent()`].

    todo!()
}

/// Verify the conclusion that the given bound is the optimal value. If we cannot conclude this
/// bound is optimal yet, an error is returned.
#[allow(unused_variables, reason = "to be implemented by students")]
pub(crate) fn verify_optimal(state: CheckingState, bound: Atomic) -> anyhow::Result<()> {
    // The state will have accumulated nogoods from all the combine steps encountered in the proof.
    // Those nogoods should collectively imply that the given bound is true. This can be tested by
    // posting the negation of the bound to the state (convert it to a context first, through
    // `state.as_context()`).

    todo!()
}
