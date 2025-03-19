use crate::model::IntVariable;
use crate::proof::checking::state::CheckingContext;

/// Verify that the provided context violates the all-different constraint.
#[allow(unused_variables, reason = "to be implemented by students")]
pub(crate) fn verify(
    variables: Vec<IntVariable>,
    context: &mut CheckingContext,
) -> anyhow::Result<()> {
    todo!()
}
