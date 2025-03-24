use std::io::Read;
use std::num::NonZero;

use anyhow::Context;
use drcp_format::reader::ProofReader;
use drcp_format::steps::Conclusion;
use drcp_format::steps::Inference;
use drcp_format::steps::Nogood;
use drcp_format::AtomicConstraint;
use drcp_format::IntAtomicConstraint;
use drcp_format::LiteralDefinitions;
use state::CheckingContext;
use state::CheckingState;

pub(crate) mod combine;
pub(crate) mod conclusion;
pub(crate) mod inferences;
pub(crate) mod state;

/// Alias for the atomic constraint type to be used in this checker.
pub(crate) type Atomic = IntAtomicConstraint<String>;

/// Verify whether the given proof is valid for the given model. If it is not, the `Err` variant of
/// [`anyhow::Result`] is returned.
#[allow(unused_variables, reason = "will be used in assignment")]
pub(crate) fn verify_proof<R>(
    state: CheckingState,
    proof: ProofReader<R, LiteralDefinitions<String>>,
) -> anyhow::Result<()>
where
    R: Read,
{
    // We go over the proof step-by-step. Each individual step must be valid for the entire proof
    // to be valid.
    //
    // A few notes to help with the implementation:
    // - Use `ProofReader::next_step()` to get the next step from the proof.
    // - Use the `verify_{inference|nogood|conclusion}()` functions in this file to dispatch to the
    //   correct verification procedures.
    // - The `drcp_format::Step::Delete` variant can be ignored. Even if the solver produces
    //   deletion steps, ignoring them does not impact the correctness of the checker.
    // - When a fact is successfully checked, use `CheckingState::record_{nogood|inference}()` to
    //   save it to the state. This way they can be used in the combine step through
    //   `CheckingState::propagate_step()`.

    todo!()
}

#[allow(dead_code, reason = "will be used in assignment")]
fn verify_conclusion(
    conclusion: Conclusion<AtomicConstraint<String>>,
    state: CheckingState,
) -> anyhow::Result<()> {
    match conclusion {
        Conclusion::Unsatisfiable => conclusion::verify_unsat(state),
        Conclusion::Optimal(c) => conclusion::verify_optimal(state, to_int_atomic(c)?),
    }
}

#[allow(dead_code, reason = "will be used in assignment")]
fn verify_combine(
    nogood: Nogood<Vec<AtomicConstraint<String>>, Vec<NonZero<u64>>>,
    mut context: CheckingContext<'_>,
) -> anyhow::Result<()> {
    let Nogood {
        id,
        literals,
        hints,
    } = nogood;

    let Some(step_ids) = hints else {
        anyhow::bail!("The checker requires combine steps to have hints.");
    };

    let premises: Vec<_> = literals
        .into_iter()
        .map(to_int_atomic)
        .collect::<Result<_, _>>()?;

    combine::verify(premises, step_ids, &mut context)
        .with_context(|| format!("Failed to check step {id}"))
}

#[allow(dead_code, reason = "will be used in assignment")]
fn verify_inference(
    inference: Inference<'_, Vec<AtomicConstraint<String>>, AtomicConstraint<String>>,
    context: CheckingContext,
) -> anyhow::Result<()> {
    // To verify an inference, we perform the following steps:
    // 1. We look up the constraint that produced the step, using the constraint hint (in the
    //    checker we assume `hint_constraint_id` has a value).
    // 2. We get the appropriate inference checker based on the inference label (in the checker we
    //    assume `hint_label` has a value).
    // 3. We dispatch to the appropriate inference checker.

    let Inference {
        id,
        hint_constraint_id,
        hint_label,
        premises,
        propagated,
    } = inference;

    // Looks up the constraint in the model.
    let constraint_id = hint_constraint_id
        .ok_or_else(|| anyhow::anyhow!("Missing constraint tag for step {id}"))?;
    let constraint = context
        .get_constraint_by_id(constraint_id)
        .cloned()
        .ok_or_else(|| anyhow::anyhow!("No constraint with id {constraint_id} in model"))?;

    // Get the label that identifies what kind of inference this step encodes.
    let label = hint_label.ok_or_else(|| anyhow::anyhow!("Missing label for step {id}"))?;

    // We convert the premises and propagated to integer atomic constraints. Booleans are not
    // supported in this course.
    let premises: Vec<_> = premises
        .into_iter()
        .map(to_int_atomic)
        .collect::<Result<_, _>>()?;
    let propagated = propagated.map(to_int_atomic).transpose()?;

    inferences::verify(premises, propagated, constraint, label, context)
        .with_context(|| format!("Error validating step {id}"))
}

fn to_int_atomic(premise: AtomicConstraint<String>) -> anyhow::Result<Atomic> {
    match premise {
        AtomicConstraint::Bool(_) => {
            anyhow::bail!("Only integer atomic constraints are supported.")
        }
        AtomicConstraint::Int(atomic) => Ok(atomic),
    }
}

/// Return the negation of the given atomic.
pub(crate) fn negate(atomic: &Atomic) -> Atomic {
    use drcp_format::Comparison::*;

    let IntAtomicConstraint {
        name,
        comparison,
        value,
    } = atomic;

    match comparison {
        GreaterThanEqual => IntAtomicConstraint {
            name: name.clone(),
            comparison: LessThanEqual,
            value: value - 1,
        },
        LessThanEqual => IntAtomicConstraint {
            name: name.clone(),
            comparison: GreaterThanEqual,
            value: value + 1,
        },
        Equal => IntAtomicConstraint {
            name: name.clone(),
            comparison: NotEqual,
            value: *value,
        },
        NotEqual => IntAtomicConstraint {
            name: name.clone(),
            comparison: Equal,
            value: *value,
        },
    }
}

/// Helper to construct atomic constraints quickly.
#[cfg(test)]
pub(crate) fn atomic(
    var: impl Into<String>,
    comparison: drcp_format::Comparison,
    value: i64,
) -> Atomic {
    Atomic {
        name: var.into(),
        comparison,
        value,
    }
}
