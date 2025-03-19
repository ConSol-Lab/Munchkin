use std::cmp::min;

use super::LearnedNogood;
use crate::basic_types::ClauseReference;
use crate::basic_types::Conjunction;
use crate::basic_types::ConstraintReference;
use crate::basic_types::StoredConflictInfo;
use crate::branching::Brancher;
use crate::engine::constraint_satisfaction_solver::CSPSolverState;
use crate::engine::constraint_satisfaction_solver::Counters;
use crate::engine::cp::propagation::propagation_context::HasAssignments;
use crate::engine::cp::propagation::PropagationContext;
use crate::engine::cp::reason::ReasonRef;
use crate::engine::cp::reason::ReasonStore;
use crate::engine::cp::AssignmentsInteger;
use crate::engine::cp::PropagatorQueue;
use crate::engine::cp::VariableLiteralMappings;
use crate::engine::cp::WatchListCP;
use crate::engine::predicates::predicate::Predicate;
use crate::engine::sat::AssignmentsPropositional;
use crate::engine::sat::ClausalPropagator;
use crate::engine::sat::ClauseAllocator;
use crate::engine::sat::ExplanationClauseManager;
use crate::engine::variables::Literal;
use crate::engine::SatisfactionSolverOptions;
use crate::munchkin_assert_moderate;
use crate::munchkin_assert_simple;

/// Used during conflict analysis to provide the necessary information.
/// All fields are made public for the time being for simplicity. In the future that may change.
#[allow(missing_debug_implementations, unused)]
pub(crate) struct ConflictAnalysisContext<'a> {
    pub(crate) clausal_propagator: &'a mut ClausalPropagator,
    pub(crate) variable_literal_mappings: &'a VariableLiteralMappings,
    pub(crate) assignments_integer: &'a mut AssignmentsInteger,
    pub(crate) assignments_propositional: &'a mut AssignmentsPropositional,
    pub(crate) internal_parameters: &'a mut SatisfactionSolverOptions,
    pub(crate) assumptions: &'a Vec<Literal>,

    pub(crate) solver_state: &'a mut CSPSolverState,
    pub(crate) brancher: &'a mut dyn Brancher,
    pub(crate) clause_allocator: &'a mut ClauseAllocator,
    pub(crate) explanation_clause_manager: &'a mut ExplanationClauseManager,
    pub(crate) reason_store: &'a mut ReasonStore,
    pub(crate) counters: &'a mut Counters,

    pub(crate) propositional_trail_index: &'a mut usize,
    pub(crate) propagator_queue: &'a mut PropagatorQueue,
    pub(crate) watch_list_cp: &'a mut WatchListCP,
    pub(crate) sat_trail_synced_position: &'a mut usize,
    pub(crate) cp_trail_synced_position: &'a mut usize,
}

impl ConflictAnalysisContext<'_> {
    /// Log a learned nogood to the proof.
    #[allow(unused, reason = "will be used in an assignment")]
    pub(crate) fn log_learned_nogood(&mut self, nogood: &LearnedNogood) {
        let _ = self
            .internal_parameters
            .proof
            .log_nogood(nogood.literals.iter().copied(), []);
    }

    /// Enqueue a decision literal as if it was a decision
    #[allow(unused, reason = "will be used in an assignment")]
    pub(crate) fn enqueue_decision_literal(&mut self, decision_literal: Literal) {
        self.assignments_propositional
            .enqueue_decision_literal(decision_literal)
    }

    /// Enqueue a literal as if it was a propagation with an empty reason
    pub(crate) fn enqueue_propagated_literal(&mut self, propagated_literal: Literal) {
        let result = self
            .assignments_propositional
            .enqueue_propagated_literal(propagated_literal, ConstraintReference::NON_REASON);
        munchkin_assert_simple!(
            result.is_none(),
            "The propagated literal should not be assigned already"
        );
    }

    /// Adds the learned nogood
    ///
    /// Note that this method will not accept learned nogoods with less than 1 literal
    #[allow(unused, reason = "will be used in an assignment")]
    pub(crate) fn add_learned_nogood(&mut self, learned_nogood: LearnedNogood) {
        munchkin_assert_simple!(learned_nogood.literals.len() > 1, "The learned nogood should have at least 2 literals for it to be added to the clausal propagator");
        let _ = self.clausal_propagator.add_asserting_learned_clause(
            learned_nogood.to_clause(),
            self.assignments_propositional,
            self.clause_allocator,
        );
    }

    /// Backtrack to the provided decision level
    pub(crate) fn backtrack(&mut self, backtrack_level: usize) {
        munchkin_assert_simple!(backtrack_level < self.get_decision_level());

        let unassigned_literals = self.assignments_propositional.synchronise(backtrack_level);

        unassigned_literals.for_each(|literal| {
            self.brancher.on_unassign_literal(literal);
        });

        self.clausal_propagator
            .synchronise(self.assignments_propositional.num_trail_entries());

        munchkin_assert_simple!(
            self.assignments_propositional.get_decision_level()
                < self.assignments_integer.get_decision_level(),
            "assignments_propositional must be backtracked _before_ CPEngineDataStructures"
        );
        *self.propositional_trail_index = min(
            *self.propositional_trail_index,
            self.assignments_propositional.num_trail_entries(),
        );
        self.assignments_integer
            .synchronise(backtrack_level)
            .iter()
            .for_each(|(domain_id, previous_value)| {
                self.brancher
                    .on_unassign_integer(*domain_id, *previous_value)
            });

        self.reason_store.synchronise(backtrack_level);
        self.propagator_queue.clear();
        //  note that variable_literal_mappings sync should be called after the sat/cp data
        // structures backtrack
        munchkin_assert_simple!(
            *self.sat_trail_synced_position >= self.assignments_propositional.num_trail_entries()
        );
        munchkin_assert_simple!(
            *self.cp_trail_synced_position >= self.assignments_integer.num_trail_entries()
        );
        *self.cp_trail_synced_position = self.assignments_integer.num_trail_entries();
        *self.sat_trail_synced_position = self.assignments_propositional.num_trail_entries();
    }

    /// Returns the last decision which was made
    pub(crate) fn get_last_decision(&self) -> Literal {
        self.assignments_propositional
            .get_last_decision()
            .expect("Expected to be able to get the last decision")
    }

    // Returns the current decision level
    pub(crate) fn get_decision_level(&self) -> usize {
        munchkin_assert_moderate!(
            self.assignments_propositional.get_decision_level()
                == self.assignments_integer.get_decision_level()
        );
        self.assignments_propositional.get_decision_level()
    }

    /// Returns the literal which was set at trail entry `index`
    #[allow(unused, reason = "will be used in an assignment")]
    pub(crate) fn get_trail_entry(&self, index: usize) -> Literal {
        self.assignments_propositional.get_trail_entry(index)
    }

    /// Returns whether the provided [`Literal`] was assigned at the root level
    #[allow(unused, reason = "will be used in an assignment")]
    pub(crate) fn is_root_level_assignment(&self, literal: Literal) -> bool {
        self.assignments_propositional
            .is_literal_root_assignment(literal)
    }

    /// Returns whether the provided [`Literal`] was a decision
    #[allow(unused, reason = "will be used in an assignment")]
    pub(crate) fn is_literal_decision(&self, literal: Literal) -> bool {
        self.assignments_propositional.is_literal_decision(literal)
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

    /// Returns the reason for the current conflict in the form `l_1 /\ ... /\ l_n -> false`
    #[allow(unused, reason = "will be used in an assignment")]
    pub(crate) fn get_conflict_nogood(&mut self) -> Conjunction {
        let clause_reference = self.get_conflict_reason_clause_reference();
        self.clause_allocator[clause_reference]
            .get_literal_slice()
            .iter()
            .copied()
            .map(|literal| !literal)
            .collect::<Vec<_>>()
            .into()
    }

    /// Returns the assignment level of the provided literal
    #[allow(unused, reason = "will be used in an assignment")]
    pub(crate) fn get_assignment_level_for_literal(&self, literal: Literal) -> usize {
        self.assignments_propositional
            .get_literal_assignment_level(literal)
    }

    /// Returns the total number of trail entries
    #[allow(unused, reason = "will be used in an assignment")]
    pub(crate) fn get_num_trail_entries(&self) -> usize {
        self.assignments_propositional.num_trail_entries()
    }
}

impl HasAssignments for ConflictAnalysisContext<'_> {
    fn assignments_integer(&self) -> &AssignmentsInteger {
        self.assignments_integer
    }

    fn assignments_propositional(&self) -> &AssignmentsPropositional {
        self.assignments_propositional
    }
}

/// Private retrieval methods
impl ConflictAnalysisContext<'_> {
    /// Given a propagated literal, returns a clause reference of the clause that propagates the
    /// literal. In case the literal was propagated by a clause, the propagating clause is
    /// returned. Otherwise, the literal was propagated by a propagator, in which case a new
    /// clause will be constructed based on the explanation given by the propagator.
    ///
    /// Note that information about the reason for propagation of root literals is not properly
    /// kept, so asking about the reason for a root propagation will cause a panic.
    ///
    /// *Note* - The `0th` [`Literal`] in the clause represents the literal that was propagated.
    fn get_propagation_clause_reference(&mut self, propagated_literal: Literal) -> ClauseReference {
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

    /// Returns a clause reference of the clause that explains the current conflict in the solver.
    /// In case the conflict was caused by an unsatisfied clause, the conflict clause is returned.
    /// Otherwise, the conflict was caused by a propagator, in which case a new clause will be
    /// constructed based on the explanation given by the propagator.
    ///
    /// Note that the solver will panic in case the solver is not in conflicting state.
    fn get_conflict_reason_clause_reference(&mut self) -> ClauseReference {
        match self.solver_state.get_conflict_info() {
            StoredConflictInfo::VirtualBinaryClause { lit1, lit2 } => self
                .explanation_clause_manager
                .add_explanation_clause_unchecked(vec![*lit1, *lit2], self.clause_allocator),
            StoredConflictInfo::Propagation { literal, reference } => {
                if reference.is_clause() {
                    reference.as_clause_reference()
                } else {
                    self.create_clause_from_propagation_reason(*literal, reference.get_reason_ref())
                }
            }
            StoredConflictInfo::Explanation {
                propagator: _,
                conjunction,
            } => {
                // create the explanation clause
                //  allocate a fresh vector each time might be a performance bottleneck
                //  todo better ways
                let explanation_literals: Vec<Literal> = conjunction
                    .iter()
                    .map(|&predicate| {
                        let literal = match predicate {
                                            Predicate::IntegerPredicate(integer_predicate) => {
                                                !self.variable_literal_mappings.get_literal(
                                                    integer_predicate,
                                                    self.assignments_propositional,
                                                    self.assignments_integer,
                                                )
                                            }
                                            bool_predicate => !bool_predicate
                                                .get_literal_of_bool_predicate(
                                                    self.assignments_propositional.true_literal,
                                                )
                                                .unwrap(),
                                        };
                        assert!(
                            self.assignments_propositional.is_literal_assigned(literal),
                            "One of the literals in the reported conflict is not assigned; please check your conflict explanations"
                        );
                        literal
                    })
                    .collect();

                if explanation_literals.len() < 2 {
                    panic!("Explanation for a conflict contained fewer than 2 literals; this could be an indication that conflict explanations have not been implemented yet")
                }

                self.explanation_clause_manager
                    .add_explanation_clause_unchecked(explanation_literals, self.clause_allocator)
            }
        }
    }

    /// Used internally to create a clause from a reason that references a propagator.
    /// This function also performs the necessary clausal allocation.
    fn create_clause_from_propagation_reason(
        &mut self,
        propagated_literal: Literal,
        reason_ref: ReasonRef,
    ) -> ClauseReference {
        let propagation_context = PropagationContext::new(
            self.assignments_integer,
            self.assignments_propositional,
            self.internal_parameters
                .use_non_generic_conflict_explanation,
            self.internal_parameters
                .use_non_generic_propagation_explanation,
        );
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
                let literal = match predicate {
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
                };
                assert!(
                    self.assignments_propositional.is_literal_assigned(literal),
                    "All literals in the reason of a propagation should be true; please check your propagation explanations"
                );
                literal
            }))
            .collect();

        if explanation_literals.len() < 2 {
            panic!("Explanation for a propagation contained fewer than 1 literal; this could be an indication that propagations explanations have not been implemented yet")
        }

        self.explanation_clause_manager
            .add_explanation_clause_unchecked(explanation_literals, self.clause_allocator)
    }
}

impl Drop for ConflictAnalysisContext<'_> {
    fn drop(&mut self) {
        // We perform the clean up of explanation clauses whenever the conflict analysis context is
        // dropped
        self.explanation_clause_manager
            .clean_up_explanation_clauses(self.clause_allocator);
    }
}
