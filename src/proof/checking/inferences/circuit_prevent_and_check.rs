use crate::model::IntVariable;
use crate::proof::checking::state::CheckingContext;

/// Verify that the provided inference is a valid prevent-and-check inference for circuit.
///
/// Note: In case the propagator triggered a conflict explicitly, `propagated` will be [`None`].
#[allow(unused_variables, reason = "to be implemented by students")]
pub(crate) fn verify(
    variables: Vec<IntVariable>,
    context: &mut CheckingContext,
) -> anyhow::Result<()> {
    todo!()
}
