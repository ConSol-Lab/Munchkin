#![cfg(test)]

use crate::model::Model;
use crate::proof::checking::negate;
use crate::proof::checking::state::CheckingContext;
use crate::proof::checking::state::CheckingState;
use crate::proof::checking::Atomic;

pub(crate) mod all_different;
pub(crate) mod circuit_prevent_and_check;
pub(crate) mod cumulative_time_table;
pub(crate) mod element;
pub(crate) mod maximum;

pub(crate) fn test_step_checker(
    model: Model,
    execute: impl FnOnce(&mut CheckingContext) -> anyhow::Result<()>,
    premises: Vec<Atomic>,
    propagated: Option<Atomic>,
    validity: Validity,
) {
    let mut state = CheckingState::from(model);
    let mut context = state.as_context();

    premises
        .iter()
        .try_for_each(|premise| context.apply(premise))
        .unwrap();

    if let Some(propagated) = propagated {
        context.apply(&negate(&propagated)).unwrap();
    }

    let result = execute(&mut context);

    match validity {
        Validity::Valid => result.expect("valid inference"),
        Validity::Invalid => {
            let _ = result.expect_err("invalid inference");
        }
    };
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Validity {
    Valid,
    Invalid,
}
