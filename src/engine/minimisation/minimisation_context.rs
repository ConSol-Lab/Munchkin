use crate::basic_types::ClauseReference;
use crate::basic_types::Conjunction;
use crate::engine::cp::propagation::propagation_context::HasAssignments;
use crate::engine::cp::propagation::PropagationContext;
use crate::engine::cp::reason::ReasonRef;
use crate::engine::cp::reason::ReasonStore;
use crate::engine::cp::AssignmentsInteger;
use crate::engine::cp::VariableLiteralMappings;
use crate::engine::sat::AssignmentsPropositional;
use crate::engine::sat::ClausalPropagator;
use crate::engine::sat::ClauseAllocator;
use crate::engine::sat::ExplanationClauseManager;
use crate::munchkin_assert_moderate;
use crate::predicates::IntegerPredicate;
use crate::predicates::Predicate;
use crate::variables::Literal;

#[derive(Debug)]
pub(crate) struct MinimisationContext<'a> {
    pub(crate) assignments_integer: &'a AssignmentsInteger,
    pub(crate) assignments_propositional: &'a AssignmentsPropositional,
    #[allow(unused, reason = "will be used in the assignments")]
    variable_literal_mappings: &'a VariableLiteralMappings,

    pub(crate) explanation_clause_manager: &'a mut ExplanationClauseManager,
    pub(crate) reason_store: &'a mut ReasonStore,
    pub(crate) clausal_propagator: &'a ClausalPropagator,
    pub(crate) clause_allocator: &'a mut ClauseAllocator,
}

impl<'a> MinimisationContext<'a> {
    pub(crate) fn new(
        assignments_integer: &'a AssignmentsInteger,
        assignments_propositional: &'a AssignmentsPropositional,
        variable_literal_mappings: &'a VariableLiteralMappings,

        explanation_clause_manager: &'a mut ExplanationClauseManager,
        reason_store: &'a mut ReasonStore,
        clausal_propagator: &'a ClausalPropagator,
        clause_allocator: &'a mut ClauseAllocator,
    ) -> Self {
        Self {
            assignments_integer,
            assignments_propositional,
            variable_literal_mappings,
            explanation_clause_manager,
            reason_store,
            clausal_propagator,
            clause_allocator,
        }
    }

    #[allow(unused, reason = "will be used in the assignments")]
    pub(crate) fn get_predicates_for_literal(
        &self,
        literal: Literal,
    ) -> impl Iterator<Item = IntegerPredicate> + '_ {
        self.variable_literal_mappings
            .get_predicates_for_literal(literal)
    }

    /// Returns the reason for the provided `literal` in the form `l_1 /\ ... /\ l_n -> literal`
    #[allow(unused, reason = "will be used in an assignment")]
    pub(crate) fn get_reason(&mut self, literal: Literal) -> Conjunction {
        let clause_reference = self.get_propagation_clause_reference(literal);
        // 0-th literal is the propagated literal so it is skipped
        self.clause_allocator[clause_reference].get_literal_slice()[1..]
            .iter()
            .copied()
            .map(|literal| !literal)
            .collect::<Vec<_>>()
            .into()
    }
}

/// Private helper methods
impl MinimisationContext<'_> {
    /// Given a propagated literal, returns a clause reference of the clause that propagates the
    /// literal. In case the literal was propagated by a clause, the propagating clause is
    /// returned. Otherwise, the literal was propagated by a propagator, in which case a new
    /// clause will be constructed based on the explanation given by the propagator.
    ///
    /// Note that information about the reason for propagation of root literals is not properly
    /// kept, so asking about the reason for a root propagation will cause a panic.
    ///
    /// *Note* - The `0th` [`Literal`] in the clause represents the literal that was propagated.
    #[allow(unused, reason = "will be used in an assignment")]
    pub(crate) fn get_propagation_clause_reference(
        &mut self,
        propagated_literal: Literal,
    ) -> ClauseReference {
        munchkin_assert_moderate!(
            !self
                .assignments_propositional
                .is_literal_root_assignment(propagated_literal),
            "Reasons are not kept properly for root propagations."
        );
        munchkin_assert_moderate!(
            self.assignments_propositional
                .is_literal_assigned_true(propagated_literal),
            "Reason for propagation only makes sense for true literals."
        );

        let constraint_reference = self
            .assignments_propositional
            .get_variable_reason_constraint(propagated_literal.get_propositional_variable());

        // Case 1: the literal was propagated by the clausal propagator
        if constraint_reference.is_clause() {
            self.clausal_propagator
                .get_literal_propagation_clause_reference(
                    propagated_literal,
                    self.assignments_propositional,
                )
        }
        // Case 2: the literal was placed on the propositional trail while synchronising the CP
        // trail with the propositional trail
        else {
            self.create_clause_from_propagation_reason(
                propagated_literal,
                constraint_reference.get_reason_ref(),
            )
        }
    }

    /// Used internally to create a clause from a reason that references a propagator.
    /// This function also performs the necessary clausal allocation.
    fn create_clause_from_propagation_reason(
        &mut self,
        propagated_literal: Literal,
        reason_ref: ReasonRef,
    ) -> ClauseReference {
        let propagation_context =
            PropagationContext::new(self.assignments_integer, self.assignments_propositional);
        let reason = self
            .reason_store
            .get_or_compute(reason_ref, &propagation_context)
            .expect("reason reference should not be stale");
        // create the explanation clause
        //  allocate a fresh vector each time might be a performance bottleneck
        //  todo better ways
        // important to keep propagated literal at the zero-th position
        let explanation_literals: Vec<Literal> = std::iter::once(propagated_literal)
            .chain(reason.iter().map(|&predicate| {
                match predicate {
                    Predicate::IntegerPredicate(integer_predicate) => {
                        !self.variable_literal_mappings.get_literal(
                            integer_predicate,
                            self.assignments_propositional,
                            self.assignments_integer,
                        )
                    }
                    bool_predicate => !bool_predicate
                        .get_literal_of_bool_predicate(self.assignments_propositional.true_literal)
                        .unwrap(),
                }
            }))
            .collect();

        self.explanation_clause_manager
            .add_explanation_clause_unchecked(explanation_literals, self.clause_allocator)
    }
}

impl HasAssignments for MinimisationContext<'_> {
    fn assignments_integer(&self) -> &AssignmentsInteger {
        self.assignments_integer
    }

    fn assignments_propositional(&self) -> &AssignmentsPropositional {
        self.assignments_propositional
    }
}

impl Drop for MinimisationContext<'_> {
    fn drop(&mut self) {
        // We perform the clean up of explanation clauses whenever the conflict analysis context is
        // dropped
        self.explanation_clause_manager
            .clean_up_explanation_clauses(self.clause_allocator);
    }
}
