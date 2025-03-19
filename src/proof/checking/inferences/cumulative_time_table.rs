use crate::model::IntVariable;
use crate::proof::checking::state::CheckingContext;

/// Verify that the provided context violates the cumulative constraint.
#[allow(unused_variables, reason = "to be implemented by students")]
pub(crate) fn verify(
    start_times: Vec<IntVariable>,
    durations: Vec<u32>,
    resource_requirements: Vec<u32>,
    resource_capacity: u32,
    context: &mut CheckingContext,
) -> anyhow::Result<()> {
    todo!()
}
