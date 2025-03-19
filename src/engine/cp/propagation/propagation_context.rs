use super::PropagatorId;
use crate::basic_types::ConstraintReference;
use crate::basic_types::Inconsistency;
use crate::engine::cp::reason::Reason;
use crate::engine::cp::reason::ReasonStore;
use crate::engine::cp::AssignmentsInteger;
use crate::engine::cp::EmptyDomain;
use crate::engine::predicates::predicate::Predicate;
use crate::engine::sat::AssignmentsPropositional;
use crate::engine::variables::IntegerVariable;
use crate::engine::variables::Literal;
use crate::munchkin_assert_simple;

/// [`PropagationContext`] is passed to propagators during propagation.
/// It may be queried to retrieve information about the current variable domains such as the
/// lower-bound of a particular variable, or used to apply changes to the domain of a variable
/// e.g. set `[x >= 5]`.
///
///
/// Note that the [`PropagationContext`] is the only point of communication beween
/// the propagations and the solver during propagation.
#[derive(Clone, Copy, Debug)]
pub struct PropagationContext<'a> {
    assignments_integer: &'a AssignmentsInteger,
    assignments_propositional: &'a AssignmentsPropositional,

    pub use_non_generic_conflict_explanation: bool,
    pub use_non_generic_propagation_explanation: bool,
}

impl<'a> PropagationContext<'a> {
    pub fn new(
        assignments_integer: &'a AssignmentsInteger,
        assignments_propositional: &'a AssignmentsPropositional,
        use_non_generic_conflict_explanation: bool,
        use_non_generic_propagation_explanation: bool,
    ) -> Self {
        PropagationContext {
            assignments_integer,
            assignments_propositional,
            use_non_generic_conflict_explanation,
            use_non_generic_propagation_explanation,
        }
    }

    /// Returns the assignment level of the provided literal
    #[allow(unused, reason = "will be used in an assignment")]
    pub(crate) fn get_assignment_level_for_literal(&self, literal: Literal) -> usize {
        self.assignments_propositional
            .get_literal_assignment_level(literal)
    }
}

#[derive(Debug)]
pub struct PropagationContextMut<'a> {
    assignments_integer: &'a mut AssignmentsInteger,
    reason_store: &'a mut ReasonStore,
    assignments_propositional: &'a mut AssignmentsPropositional,
    propagator: PropagatorId,

    reification_literal: Option<Literal>,
    pub use_non_generic_conflict_explanation: bool,
    pub use_non_generic_propagation_explanation: bool,
}

impl<'a> PropagationContextMut<'a> {
    pub fn new(
        assignments_integer: &'a mut AssignmentsInteger,
        reason_store: &'a mut ReasonStore,
        assignments_propositional: &'a mut AssignmentsPropositional,
        propagator: PropagatorId,
        use_non_generic_conflict_explanation: bool,
        use_non_generic_propagation_explanation: bool,
    ) -> Self {
        PropagationContextMut {
            assignments_integer,
            reason_store,
            assignments_propositional,
            propagator,
            reification_literal: None,
            use_non_generic_conflict_explanation,
            use_non_generic_propagation_explanation,
        }
    }

    /// Apply a reification literal to all the explanations that are passed to the context.
    pub(crate) fn with_reification(&mut self, reification_literal: Literal) {
        munchkin_assert_simple!(
            self.reification_literal.is_none(),
            "cannot reify an already reified propagation context"
        );

        self.reification_literal = Some(reification_literal);
    }

    fn build_reason(&self, reason: Reason) -> Reason {
        if let Some(reification_literal) = self.reification_literal {
            match reason {
                Reason::Eager(mut conjunction) => {
                    conjunction.add(reification_literal.into());
                    Reason::Eager(conjunction)
                }
                Reason::Lazy(callback) => {
                    Reason::Lazy(Box::new(move |context: &PropagationContext| {
                        let mut conjunction = callback.compute(context);
                        conjunction.add(reification_literal.into());
                        conjunction
                    }))
                }
            }
        } else {
            reason
        }
    }

    pub(crate) fn as_readonly(&self) -> PropagationContext<'_> {
        PropagationContext {
            assignments_integer: self.assignments_integer,
            assignments_propositional: self.assignments_propositional,
            use_non_generic_conflict_explanation: self.use_non_generic_conflict_explanation,
            use_non_generic_propagation_explanation: self.use_non_generic_propagation_explanation,
        }
    }
}

/// A trait which defines common methods for retrieving the [`AssignmentsInteger`] and
/// [`AssignmentsPropositional`] from the structure which implements this trait.
pub trait HasAssignments {
    /// Returns the stored [`AssignmentsInteger`].
    fn assignments_integer(&self) -> &AssignmentsInteger;

    /// Returns the stored [`AssignmentsPropositional`].
    fn assignments_propositional(&self) -> &AssignmentsPropositional;
}

mod private {
    use super::*;

    impl HasAssignments for PropagationContext<'_> {
        fn assignments_integer(&self) -> &AssignmentsInteger {
            self.assignments_integer
        }

        fn assignments_propositional(&self) -> &AssignmentsPropositional {
            self.assignments_propositional
        }
    }

    impl HasAssignments for PropagationContextMut<'_> {
        fn assignments_integer(&self) -> &AssignmentsInteger {
            self.assignments_integer
        }

        fn assignments_propositional(&self) -> &AssignmentsPropositional {
            self.assignments_propositional
        }
    }
}

#[allow(unused, reason = "could be used in an assignment")]
pub(crate) trait ReadDomains: HasAssignments {
    fn is_literal_fixed(&self, var: Literal) -> bool {
        self.assignments_propositional().is_literal_assigned(var)
    }

    fn is_literal_true(&self, var: Literal) -> bool {
        self.assignments_propositional()
            .is_literal_assigned_true(var)
    }

    fn get_assignment_level_for_literal(&self, literal: Literal) -> usize {
        self.assignments_propositional()
            .get_literal_assignment_level(literal)
    }

    /// Returns `true` if the domain of the given variable is singleton.
    fn is_fixed<Var: IntegerVariable>(&self, var: &Var) -> bool {
        self.lower_bound(var) == self.upper_bound(var)
    }

    fn lower_bound<Var: IntegerVariable>(&self, var: &Var) -> i32 {
        var.lower_bound(self.assignments_integer())
    }

    fn upper_bound<Var: IntegerVariable>(&self, var: &Var) -> i32 {
        var.upper_bound(self.assignments_integer())
    }

    fn contains<Var: IntegerVariable>(&self, var: &Var, value: i32) -> bool {
        var.contains(self.assignments_integer(), value)
    }

    fn describe_domain<Var: IntegerVariable>(&self, var: &Var) -> Vec<Predicate> {
        var.describe_domain(self.assignments_integer())
    }
}

impl<T: HasAssignments> ReadDomains for T {}

impl PropagationContextMut<'_> {
    pub fn remove<Var: IntegerVariable, R: Into<Reason>>(
        &mut self,
        var: &Var,
        value: i32,
        reason: R,
    ) -> Result<(), EmptyDomain> {
        if var.contains(self.assignments_integer, value) {
            let reason = self.build_reason(reason.into());
            let reason_ref = self.reason_store.push(self.propagator, reason);
            return var.remove(self.assignments_integer, value, Some(reason_ref));
        }
        Ok(())
    }

    pub fn set_upper_bound<Var: IntegerVariable, R: Into<Reason>>(
        &mut self,
        var: &Var,
        bound: i32,
        reason: R,
    ) -> Result<(), EmptyDomain> {
        if bound < var.upper_bound(self.assignments_integer) {
            let reason = self.build_reason(reason.into());
            let reason_ref = self.reason_store.push(self.propagator, reason);
            return var.set_upper_bound(self.assignments_integer, bound, Some(reason_ref));
        }
        Ok(())
    }

    pub fn set_lower_bound<Var: IntegerVariable, R: Into<Reason>>(
        &mut self,
        var: &Var,
        bound: i32,
        reason: R,
    ) -> Result<(), EmptyDomain> {
        if bound > var.lower_bound(self.assignments_integer) {
            let reason = self.build_reason(reason.into());
            let reason_ref = self.reason_store.push(self.propagator, reason);
            return var.set_lower_bound(self.assignments_integer, bound, Some(reason_ref));
        }
        Ok(())
    }

    pub fn assign_literal<R: Into<Reason>>(
        &mut self,
        var: Literal,
        bound: bool,
        reason: R,
    ) -> Result<(), Inconsistency> {
        if !self.assignments_propositional.is_literal_assigned(var) {
            let reason = self.build_reason(reason.into());
            let reason_ref = self.reason_store.push(self.propagator, reason);
            let enqueue_result = self.assignments_propositional.enqueue_propagated_literal(
                if bound { var } else { !var },
                ConstraintReference::create_reason_reference(reason_ref),
            );
            if let Some(conflict_info) = enqueue_result {
                return Err(Inconsistency::Other(conflict_info));
            }
        }

        Ok(())
    }
}
