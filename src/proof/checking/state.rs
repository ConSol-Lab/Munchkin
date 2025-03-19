use std::collections::BTreeMap;
use std::num::NonZero;

use drcp_format::steps::StepId;
use drcp_format::IntAtomicConstraint;

use super::negate;
use super::Atomic;
use crate::engine::cp::AssignmentsInteger;
use crate::model::Constraint;
use crate::model::IntVariable;
use crate::model::Model;
use crate::model::VariableMap;
use crate::predicate;
use crate::predicates::IntegerPredicate;
use crate::variables::IntegerVariable;

/// The domains of the variables in the model. To temporarily modify domains, use
/// [`Self::as_context`] to obtain an instance of [`CheckingContext`].
pub(crate) struct CheckingState {
    model: Model,
    assignment: AssignmentsInteger,
    variable_map: VariableMap,
    nogoods: BTreeMap<StepId, Vec<Atomic>>,
    inferences: BTreeMap<StepId, (Vec<Atomic>, Option<Atomic>)>,
}

impl From<Model> for CheckingState {
    fn from(model: Model) -> Self {
        let (assignment, variable_map) = model.to_assignment();

        CheckingState {
            model,
            assignment,
            variable_map,
            nogoods: BTreeMap::default(),
            inferences: BTreeMap::default(),
        }
    }
}

#[allow(unused, reason = "will be used in the assignment")]
impl CheckingState {
    /// Create a [`CheckingContext`] for the current state.
    pub(crate) fn as_context(&mut self) -> CheckingContext<'_> {
        self.assignment.increase_decision_level();

        CheckingContext {
            model: &self.model,
            assignment: &mut self.assignment,
            variable_map: &self.variable_map,
            nogoods: &self.nogoods,
            inferences: &self.inferences,
        }
    }

    /// Tests whether the nogood `true -> false` has been recorded.
    pub(crate) fn is_inconsistent(&self) -> bool {
        self.nogoods
            .iter()
            .rev()
            .any(|(_, nogood)| nogood.is_empty())
    }

    /// Record a nogood to the state. This can be used to propagate using
    /// [`CheckingContext::propagate_step`]. If another nogood or inference was already registered
    /// with this step id, then an error is returned.
    pub(crate) fn record_nogood(
        &mut self,
        step_id: StepId,
        nogood: Vec<Atomic>,
    ) -> anyhow::Result<()> {
        if self.inferences.contains_key(&step_id) {
            anyhow::bail!("Step id {step_id} is recorded multiple times.")
        }

        match self.nogoods.insert(step_id, nogood) {
            Some(_) => anyhow::bail!("Step id {step_id} is recorded multiple times."),
            None => Ok(()),
        }
    }

    /// Record a nogood to the state. This can be used to propagate using
    /// [`CheckingContext::propagate_step`]. If another nogood or inference was already registered
    /// with this step id, then an error is returned.
    pub(crate) fn record_inference(
        &mut self,
        step_id: StepId,
        premises: Vec<Atomic>,
        conclusion: Option<Atomic>,
    ) -> anyhow::Result<()> {
        if self.nogoods.contains_key(&step_id) {
            anyhow::bail!("Step id {step_id} is recorded multiple times.")
        }

        match self.inferences.insert(step_id, (premises, conclusion)) {
            Some(_) => anyhow::bail!("Step id {step_id} is recorded multiple times."),
            None => Ok(()),
        }
    }
}

/// A snapshot of the checking state. Step checkers can modify the domains of variables through
/// this context, and when it is dropped, the state will be restored to the state when the context
/// was initially created.
pub(crate) struct CheckingContext<'a> {
    model: &'a Model,
    variable_map: &'a VariableMap,
    assignment: &'a mut AssignmentsInteger,
    nogoods: &'a BTreeMap<StepId, Vec<Atomic>>,
    inferences: &'a BTreeMap<StepId, (Vec<Atomic>, Option<Atomic>)>,
}

#[allow(unused, reason = "will be used in the assignment")]
impl CheckingContext<'_> {
    /// Apply the given atomic to the context.
    ///
    /// Returns an error in one of the following cases:
    /// - If it is mutually exclusive with previously applied atomics, or the initial domain of the
    ///   variable, then an error is returned.
    /// - If the atomic references a variable that does not exist in the model.
    pub(crate) fn apply(&mut self, atomic: &Atomic) -> anyhow::Result<()> {
        let predicate = to_integer_predicate(self.variable_map, atomic)?;
        self.assignment.apply_integer_predicate(predicate, None)?;

        Ok(())
    }

    /// Get the lower bound of the given integer variable.
    pub(crate) fn lower_bound(&self, variable: IntVariable) -> i32 {
        let variable = self.variable_map.to_solver_variable(variable);
        variable.lower_bound(self.assignment)
    }

    /// Get the upper bound of the given integer variable.
    pub(crate) fn upper_bound(&self, variable: IntVariable) -> i32 {
        let variable = self.variable_map.to_solver_variable(variable);
        variable.upper_bound(self.assignment)
    }

    /// Test whether the given value is in the domain of the variable.
    pub(crate) fn contains(&self, variable: IntVariable, value: i32) -> bool {
        let variable = self.variable_map.to_solver_variable(variable);
        variable.contains(self.assignment, value)
    }

    /// If the variable is fixed, this returns the value it is fixed to. Otherwise, it returns
    /// [`None`].
    pub(crate) fn fixed_value(&self, variable: IntVariable) -> Option<i32> {
        let variable = self.variable_map.to_solver_variable(variable);

        if variable.is_fixed(self.assignment) {
            Some(variable.upper_bound(self.assignment))
        } else {
            None
        }
    }

    /// Get the constraint from the model with the given ID.
    pub(crate) fn get_constraint_by_id(&self, constraint_id: NonZero<u32>) -> Option<&Constraint> {
        self.model.get_constraint_by_id(constraint_id)
    }

    /// Propagate a step identified with the given ID. If successful, this returns either a new
    /// [`Atomic`] or a conflict (modelled through [`StepPropagation`]. If not all the premises of
    /// the step are fulfilled, [`Err`] is returned.
    pub(crate) fn propagate_step(&self, step_id: NonZero<u64>) -> anyhow::Result<StepPropagation> {
        if let Some((premises, consequence)) = self.inferences.get(&step_id) {
            return self.propagate_inference(premises, consequence.as_ref());
        }

        if let Some(atomics) = self.nogoods.get(&step_id) {
            return self.propagate_nogood(atomics);
        }

        anyhow::bail!("No step with id {step_id} exists")
    }

    fn propagate_inference(
        &self,
        premises: &[Atomic],
        conclusion: Option<&Atomic>,
    ) -> anyhow::Result<StepPropagation> {
        let all_premises_hold = premises.iter().all(|atomic| {
            let predicate = to_integer_predicate(self.variable_map, atomic)
                .expect("previous stages would have failed if this was not possible");

            self.assignment.does_integer_predicate_hold(predicate)
        });

        if !all_premises_hold {
            anyhow::bail!("Cannot propagate because not all premises are true.")
        }

        match conclusion {
            Some(atomic) => Ok(StepPropagation::Atomic(atomic.clone())),
            None => Ok(StepPropagation::Conflict),
        }
    }

    fn propagate_nogood(&self, nogood: &[Atomic]) -> anyhow::Result<StepPropagation> {
        let assigned_count = nogood
            .iter()
            .filter(|atomic| {
                let predicate = to_integer_predicate(self.variable_map, atomic)
                    .expect("previous stages would have failed if this was not possible");

                self.assignment.does_integer_predicate_hold(predicate)
            })
            .count();

        let unassigned_atomic = nogood.iter().find(|atomic| {
            let predicate = to_integer_predicate(self.variable_map, atomic)
                .expect("previous stages would have failed if this was not possible");

            !self.assignment.does_integer_predicate_hold(predicate)
        });

        match unassigned_atomic {
            Some(atomic) => {
                if assigned_count != nogood.len() - 1 {
                    anyhow::bail!("Nogood does not propagate anything.")
                }

                Ok(StepPropagation::Atomic(negate(atomic)))
            }
            None => Ok(StepPropagation::Conflict),
        }
    }
}
/// Map the atomic constraint from the proof to a Munchkin predicate.
fn to_integer_predicate(
    variable_map: &VariableMap,
    atomic: &Atomic,
) -> anyhow::Result<IntegerPredicate> {
    let IntAtomicConstraint {
        name,
        comparison,
        value,
    } = atomic;

    let var = variable_map
        .get_named_variable(name)
        .ok_or_else(|| anyhow::anyhow!("Variable '{name}' does not exist"))?;
    let value: i32 = (*value).try_into().unwrap();

    let predicate = match comparison {
        drcp_format::Comparison::GreaterThanEqual => predicate![var >= value],
        drcp_format::Comparison::LessThanEqual => predicate![var <= value],
        drcp_format::Comparison::Equal => predicate![var == value],
        drcp_format::Comparison::NotEqual => predicate![var != value],
    };

    match predicate {
        crate::predicates::Predicate::IntegerPredicate(p) => Ok(p),
        _ => panic!("Only integer predicates are supported by the checker."),
    }
}

impl Drop for CheckingContext<'_> {
    fn drop(&mut self) {
        let _ = self.assignment.synchronise(0);
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
#[allow(dead_code, reason = "will be used in assignment")]
pub(crate) enum StepPropagation {
    Atomic(Atomic),
    Conflict,
}

#[cfg(test)]
mod tests {
    use drcp_format::Comparison::*;

    use super::*;
    use crate::proof::checking::atomic;

    #[test]
    fn dropping_context_restores_bounds() {
        let mut model = Model::default();
        let x = model.new_interval_variable("x", 1, 10);

        let mut state = CheckingState::from(model);

        {
            let mut context = state.as_context();
            context
                .apply(&atomic("x", GreaterThanEqual, 10))
                .expect("no conflict");
        }

        {
            let context = state.as_context();
            assert_eq!(1, context.lower_bound(x));
        }
    }

    #[test]
    fn propagate_unit_nogood() {
        let mut model = Model::default();
        let _ = model.new_interval_variable("x", 1, 10);

        let mut state = CheckingState::from(model);
        state
            .record_nogood(
                NonZero::new(1).unwrap(),
                vec![atomic("x", GreaterThanEqual, 5)],
            )
            .expect("first time this ID is used");

        let context = state.as_context();

        let consequence = context
            .propagate_step(NonZero::new(1).unwrap())
            .expect("can propagate");

        assert_eq!(
            StepPropagation::Atomic(atomic("x", LessThanEqual, 4)),
            consequence
        );
    }

    #[test]
    fn propagate_non_unit_nogood() {
        let mut model = Model::default();
        let _ = model.new_interval_variable("x", 1, 10);
        let _ = model.new_interval_variable("y", 1, 10);

        let mut state = CheckingState::from(model);

        let atom = atomic("y", LessThanEqual, 3);

        state
            .record_nogood(
                NonZero::new(1).unwrap(),
                vec![atomic("x", GreaterThanEqual, 5), atom.clone()],
            )
            .expect("first time this ID is used");

        let mut context = state.as_context();

        context.apply(&atom).expect("no conflict");
        let consequence = context
            .propagate_step(NonZero::new(1).unwrap())
            .expect("can propagate");

        assert_eq!(
            StepPropagation::Atomic(atomic("x", LessThanEqual, 4)),
            consequence
        );
    }

    #[test]
    fn nogoods_do_not_propagate_if_not_enought_atomics_are_true() {
        let mut model = Model::default();
        let _ = model.new_interval_variable("x", 1, 10);
        let _ = model.new_interval_variable("y", 1, 10);

        let mut state = CheckingState::from(model);

        let atom = atomic("y", LessThanEqual, 3);

        state
            .record_nogood(
                NonZero::new(1).unwrap(),
                vec![atomic("x", GreaterThanEqual, 5), atom],
            )
            .expect("first time this ID is used");

        let context = state.as_context();

        let _ = context
            .propagate_step(NonZero::new(1).unwrap())
            .expect_err("cannot propagate");
    }

    #[test]
    fn empty_nogood_leads_to_inconsistency() {
        let model = Model::default();
        let mut state = CheckingState::from(model);
        state
            .record_nogood(NonZero::new(1).unwrap(), vec![])
            .expect("unique ID");

        assert!(state.is_inconsistent());
    }

    #[test]
    fn cannot_record_nogood_with_existing_id() {
        let model = Model::default();
        let mut state = CheckingState::from(model);

        state
            .record_nogood(NonZero::new(1).unwrap(), vec![])
            .expect("unique ID");
        let _ = state
            .record_nogood(NonZero::new(1).unwrap(), vec![])
            .expect_err("previously encountered ID");

        state
            .record_inference(NonZero::new(2).unwrap(), vec![], None)
            .expect("unique ID");
        let _ = state
            .record_nogood(NonZero::new(2).unwrap(), vec![])
            .expect_err("previously encountered ID");
    }

    #[test]
    fn cannot_record_inference_with_existing_id() {
        let model = Model::default();
        let mut state = CheckingState::from(model);

        state
            .record_inference(NonZero::new(1).unwrap(), vec![], None)
            .expect("unique ID");
        let _ = state
            .record_inference(NonZero::new(1).unwrap(), vec![], None)
            .expect_err("previously encountered ID");

        state
            .record_nogood(NonZero::new(2).unwrap(), vec![])
            .expect("unique ID");
        let _ = state
            .record_inference(NonZero::new(2).unwrap(), vec![], None)
            .expect_err("previously encountered ID");
    }

    #[test]
    fn inferences_propagate_correctly() {
        let mut model = Model::default();
        let _ = model.new_interval_variable("x", 1, 10);
        let _ = model.new_interval_variable("y", 1, 10);

        let mut state = CheckingState::from(model);

        let premise = atomic("x", GreaterThanEqual, 5);
        let consequence = atomic("y", LessThanEqual, 3);

        state
            .record_inference(
                NonZero::new(1).unwrap(),
                vec![premise.clone()],
                Some(consequence.clone()),
            )
            .expect("first time this ID is used");

        let mut context = state.as_context();

        context.apply(&premise).expect("no conflict");
        let actual_consequence = context
            .propagate_step(NonZero::new(1).unwrap())
            .expect("can propagate");

        assert_eq!(StepPropagation::Atomic(consequence), actual_consequence);
    }

    #[test]
    fn inferences_identify_conflict() {
        let mut model = Model::default();
        let _ = model.new_interval_variable("x", 1, 10);
        let _ = model.new_interval_variable("y", 1, 10);

        let mut state = CheckingState::from(model);

        let p1 = atomic("x", GreaterThanEqual, 5);
        let p2 = atomic("y", LessThanEqual, 3);

        state
            .record_inference(NonZero::new(1).unwrap(), vec![p1.clone(), p2.clone()], None)
            .expect("first time this ID is used");

        let mut context = state.as_context();

        context.apply(&p1).expect("no conflict");
        context.apply(&p2).expect("no conflict");

        let actual_consequence = context
            .propagate_step(NonZero::new(1).unwrap())
            .expect("can propagate");

        assert_eq!(StepPropagation::Conflict, actual_consequence);
    }
}
