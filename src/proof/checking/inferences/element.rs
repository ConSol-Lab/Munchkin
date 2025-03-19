use crate::model::IntVariable;
use crate::proof::checking::state::CheckingContext;

/// Verify that the provided context violates the element constraint.
#[allow(unused_variables, reason = "to be implemented by students")]
pub(crate) fn verify(
    array: Vec<IntVariable>,
    index: IntVariable,
    rhs: IntVariable,
    context: &mut CheckingContext,
) -> anyhow::Result<()> {
    todo!()
}
