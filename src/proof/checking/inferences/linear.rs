use crate::model::IntVariable;
use crate::proof::checking::state::CheckingContext;

/// Verify that the current state in `context` violates the linear constraint.
pub(super) fn verify(
    terms: Vec<IntVariable>,
    rhs: i32,
    context: &mut CheckingContext,
) -> anyhow::Result<()> {
    let left_hand_side = terms
        .iter()
        .map(|&term| context.lower_bound(term) as i64)
        .sum::<i64>();

    if left_hand_side > rhs as i64 {
        Ok(())
    } else {
        anyhow::bail!("Right-hand side is not exceeded by left-hand side.");
    }
}

#[cfg(test)]
mod tests {
    use drcp_format::Comparison::*;

    use super::*;
    use crate::model::Model;
    use crate::proof::checking::atomic;
    use crate::proof::checking::Atomic;
    use crate::tests::proof_checking::inferences::test_step_checker;
    use crate::tests::proof_checking::inferences::Validity;

    /// Constraint `-2x + y - 2z <= 0`
    /// Inference `[x <= 0] /\ [y >= 2] -> [z >= 1]`
    #[test]
    fn positive_example_1() {
        run_verify(
            |model| {
                let x = model.new_interval_variable("x", 0, 1);
                let y = model.new_interval_variable("y", 0, 2);
                let z = model.new_interval_variable("z", 0, 1);

                (vec![x.scaled(-2), y, z.scaled(-2)], 0)
            },
            vec![
                atomic("x", LessThanEqual, 0),
                atomic("y", GreaterThanEqual, 2),
            ],
            atomic("z", GreaterThanEqual, 1),
            Validity::Valid,
        )
    }

    /// Constraint: `-2x + y + 2z >= 2`
    /// Inference: `[x >= 1] -> [z >= 1]`
    #[test]
    fn positive_example_2() {
        run_verify(
            |model| {
                let x = model.new_interval_variable("x", 0, 1);
                let y = model.new_interval_variable("y", 0, 2);
                let z = model.new_interval_variable("z", 0, 1);

                (vec![x.scaled(2), y.scaled(-1), z.scaled(2)], -2)
            },
            vec![atomic("x", GreaterThanEqual, 1)],
            atomic("z", GreaterThanEqual, 1),
            Validity::Valid,
        );
    }

    /// Constraint: `-2x + y + 2z >= 2`
    /// Inference: `[x >= 0] -> [z >= 1]`
    #[test]
    fn negative_example_1() {
        run_verify(
            |model| {
                let x = model.new_interval_variable("x", 0, 1);
                let y = model.new_interval_variable("y", 0, 2);
                let z = model.new_interval_variable("z", 0, 1);

                (vec![x.scaled(2), y.scaled(-1), z.scaled(2)], -2)
            },
            vec![atomic("x", GreaterThanEqual, 0)],
            atomic("z", GreaterThanEqual, 1),
            Validity::Invalid,
        );
    }

    fn run_verify(
        make_constraint: impl FnOnce(&mut Model) -> (Vec<IntVariable>, i32),
        premises: Vec<Atomic>,
        propagated: Atomic,
        validity: Validity,
    ) {
        let mut model = Model::default();
        let (terms, rhs) = make_constraint(&mut model);

        test_step_checker(
            model,
            move |context| verify(terms, rhs, context),
            premises,
            Some(propagated),
            validity,
        );
    }
}
