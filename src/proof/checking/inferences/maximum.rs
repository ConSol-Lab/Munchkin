use crate::model::IntVariable;
use crate::proof::checking::state::CheckingContext;

/// Verify that the provided inference is a valid maximum inference.
#[allow(unused_variables, reason = "to be implemented by students")]
pub(crate) fn verify(
    terms: Vec<IntVariable>,
    rhs: IntVariable,
    context: &mut CheckingContext,
) -> anyhow::Result<()> {
    todo!()
}
