use drcp_format::steps::StepId;

use crate::proof::checking::state::CheckingContext;
use crate::proof::checking::Atomic;

/// Verify that the given nogood is valid.
#[allow(unused_variables, reason = "to be implemented by students")]
pub(crate) fn verify(
    premises: Vec<Atomic>,
    step_ids: Vec<StepId>,
    context: &mut CheckingContext,
) -> anyhow::Result<()> {
    // Aside from posting atomics to the context, in this verification step you need to be able to
    // 'propagate' the proof steps indicated by `step_ids`. To do so, use
    // `CheckingContext::propagate_step()`.

    todo!()
}
