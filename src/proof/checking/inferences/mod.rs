use super::negate;
use super::state::CheckingContext;
use super::Atomic;
use crate::model::Constraint;
use crate::model::IntVariable;
use crate::proof::inference_labels;

pub(crate) mod all_different;
pub(crate) mod circuit_prevent_and_check;
pub(crate) mod cumulative_time_table;
pub(crate) mod element;
pub(crate) mod linear;
pub(crate) mod maximum;

/// Verify an inference step. The proof claims the inference is implied by `constraint`.
pub(super) fn verify(
    premises: Vec<Atomic>,
    propagated: Option<Atomic>,
    constraint: Constraint,
    label: &str,
    mut context: CheckingContext,
) -> anyhow::Result<()> {
    context.set_proof_step_premises(premises.clone());

    // First we apply the premises and propagated atomics.
    premises
        .iter()
        .try_for_each(|premise| context.apply(premise))
        .map_err(|_| {
            anyhow::anyhow!(
                "The premises in an inference should not contain mutually exclusive atomic constraints."
            )
        })?;

    if let Some(ref propagated) = propagated {
        context.set_proof_step_conclusion(propagated.clone());
        context.apply(&negate(propagated)).map_err(|_| {
            anyhow::anyhow!(
                "The negation of the conclusion in an inference should not be mutually exclusive with the premises."
            )
        })?;
    }

    // Then the appropriate inference checker should identify whether this is a conflicting state.
    match label {
        inference_labels::LINEAR => {
            // There are two constraints that can do linear inference:
            // - \sum x_i <= c
            // - \sum x_i == c
            //
            // In case of the latter, we re-write it here to two inequalities.
            if let Constraint::LinearEqual { terms, rhs } = constraint {
                return verify_linear_equal(terms, rhs, &mut context);
            }

            // We unpack the terms and the right-hand-side from the constraint. If it is not a
            // linear constraint, then this inference step is invalid, as no other
            // constraint produces this inference.
            //
            // Since it is already checked that the premises are the terms, we don't actually need
            // the terms in the checker.
            let Constraint::LinearLessEqual { terms, rhs } = constraint else {
                anyhow::bail!("Linear reasoning is only done in linear constraints.")
            };

            linear::verify(terms, rhs, &mut context)
        }
        inference_labels::ELEMENT => {
            let Constraint::Element { array, index, rhs } = constraint else {
                anyhow::bail!("Element reasoning is only done in the element constraint.")
            };

            element::verify(array, index, rhs, &mut context)
        }
        inference_labels::MAXIMUM => {
            let Constraint::Maximum { terms, rhs } = constraint else {
                anyhow::bail!("Maximum reasoning is only done in the maximum constraint.")
            };

            maximum::verify(terms, rhs, &mut context)
        }
        inference_labels::ALL_DIFFERENT => {
            let Constraint::Circuit(variables) = constraint else {
                // In general, one could use the all-different constraint separately from circuit as
                // well. However, in the setup of this solver, we only expect it to
                // appear when using the circuit constraint in the model.
                anyhow::bail!("All-different reasoning is only done in the circuit constraint.")
            };

            all_different::verify(variables, &mut context)
        }
        inference_labels::TIME_TABLE => {
            let Constraint::Cumulative {
                start_times,
                durations,
                resource_requirements,
                resource_capacity,
            } = constraint
            else {
                anyhow::bail!("Time-table reasoning is only done in the cumulative constraint.")
            };

            cumulative_time_table::verify(
                start_times,
                durations,
                resource_requirements,
                resource_capacity,
                &mut context,
            )
        }
        inference_labels::PREVENT_AND_CHECK => {
            let Constraint::Circuit(variables) = constraint else {
                anyhow::bail!(
                    "Circuit prevent-and-check reasoning is only done in the circuit constraint."
                )
            };

            circuit_prevent_and_check::verify(variables, &mut context)
        }

        unknown => anyhow::bail!("Unknown inference label '{unknown}'"),
    }
}

fn verify_linear_equal(
    terms: Vec<IntVariable>,
    rhs: i32,
    context: &mut CheckingContext,
) -> Result<(), anyhow::Error> {
    let flipped_terms = terms.iter().map(|var| var.scaled(-1)).collect();
    let flipped_rhs = -rhs;

    let verify_upper_bound = linear::verify(terms, rhs, context);

    let verify_lower_bound = linear::verify(flipped_terms, flipped_rhs, context);

    verify_upper_bound.or(verify_lower_bound)
}
