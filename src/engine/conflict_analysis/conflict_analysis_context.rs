use std::cmp::min;

use crate::basic_types::ClauseReference;
use crate::basic_types::ConflictInfo;
use crate::basic_types::ConstraintReference;
use crate::basic_types::StoredConflictInfo;
use crate::branching::Brancher;
use crate::engine::constraint_satisfaction_solver::CSPSolverState;
use crate::engine::constraint_satisfaction_solver::ClausalPropagatorType;
use crate::engine::constraint_satisfaction_solver::ClauseAllocatorType;
use crate::engine::constraint_satisfaction_solver::Counters;
use crate::engine::predicates::predicate::Predicate;
use crate::engine::propagation::PropagationContext;
use crate::engine::reason::ReasonRef;
use crate::engine::reason::ReasonStore;
use crate::engine::variables::Literal;
use crate::engine::AssignmentsInteger;
use crate::engine::AssignmentsPropositional;
use crate::engine::ExplanationClauseManager;
use crate::engine::PropagatorQueue;
use crate::engine::SatisfactionSolverOptions;
use crate::engine::VariableLiteralMappings;
use crate::engine::WatchListCP;
use crate::pumpkin_assert_moderate;
use crate::pumpkin_assert_simple;

/// Used during conflict analysis to provide the necessary information.
/// All fields are made public for the time being for simplicity. In the future that may change.
#[allow(missing_debug_implementations)]
pub(crate) struct ConflictAnalysisContext<'a> {
    pub(crate) clausal_propagator: &'a mut ClausalPropagatorType,
    pub(crate) variable_literal_mappings: &'a VariableLiteralMappings,
    pub(crate) assignments_integer: &'a mut AssignmentsInteger,
    pub(crate) assignments_propositional: &'a mut AssignmentsPropositional,
    pub(crate) internal_parameters: &'a SatisfactionSolverOptions,
    pub(crate) assumptions: &'a Vec<Literal>,

    pub(crate) solver_state: &'a mut CSPSolverState,
    pub(crate) brancher: &'a mut dyn Brancher,
    pub(crate) clause_allocator: &'a mut ClauseAllocatorType,
    pub(crate) explanation_clause_manager: &'a mut ExplanationClauseManager,
    pub(crate) reason_store: &'a mut ReasonStore,
    pub(crate) counters: &'a mut Counters,

    pub(crate) propositional_trail_index: &'a mut usize,
    pub(crate) propagator_queue: &'a mut PropagatorQueue,
    pub(crate) watch_list_cp: &'a mut WatchListCP,
    pub(crate) sat_trail_synced_position: &'a mut usize,
    pub(crate) cp_trail_synced_position: &'a mut usize,
}

impl<'a> ConflictAnalysisContext<'a> {
    pub(crate) fn enqueue_decision_literal(&mut self, decision_literal: Literal) {
        self.assignments_propositional
            .enqueue_decision_literal(decision_literal)
    }

    pub(crate) fn enqueue_propagated_literal(
        &mut self,
        propagated_literal: Literal,
        constraint_reference: ConstraintReference,
    ) -> Option<ConflictInfo> {
        self.assignments_propositional
            .enqueue_propagated_literal(propagated_literal, constraint_reference)
    }

    pub(crate) fn backtrack(&mut self, backtrack_level: usize) {
        pumpkin_assert_simple!(backtrack_level < self.get_decision_level());

        let unassigned_literals = self.assignments_propositional.synchronise(backtrack_level);

        unassigned_literals.for_each(|literal| {
            self.brancher.on_unassign_literal(literal);
            // TODO: We should also backtrack on the integer variables here
        });

        self.clausal_propagator
            .synchronise(self.assignments_propositional.num_trail_entries());

        pumpkin_assert_simple!(
            self.assignments_propositional.get_decision_level()
                < self.assignments_integer.get_decision_level(),
            "assignments_propositional must be backtracked _before_ CPEngineDataStructures"
        );
        *self.propositional_trail_index = min(
            *self.propositional_trail_index,
            self.assignments_propositional.num_trail_entries(),
        );
        self.assignments_integer
            .synchronise(
                backtrack_level,
                self.watch_list_cp.is_watching_any_backtrack_events(),
            )
            .iter()
            .for_each(|(domain_id, previous_value)| {
                self.brancher
                    .on_unassign_integer(*domain_id, *previous_value)
            });

        self.reason_store.synchronise(backtrack_level);
        self.propagator_queue.clear();
        //  note that variable_literal_mappings sync should be called after the sat/cp data
        // structures backtrack
        pumpkin_assert_simple!(
            *self.sat_trail_synced_position >= self.assignments_propositional.num_trail_entries()
        );
        pumpkin_assert_simple!(
            *self.cp_trail_synced_position >= self.assignments_integer.num_trail_entries()
        );
        *self.cp_trail_synced_position = self.assignments_integer.num_trail_entries();
        *self.sat_trail_synced_position = self.assignments_propositional.num_trail_entries();
    }

    pub(crate) fn get_last_decision(&self) -> Literal {
        self.assignments_propositional
            .get_last_decision()
            .expect("Expected to be able to get the last decision")
    }

    pub(crate) fn get_decision_level(&self) -> usize {
        pumpkin_assert_moderate!(
            self.assignments_propositional.get_decision_level()
                == self.assignments_integer.get_decision_level()
        );
        self.assignments_propositional.get_decision_level()
    }

    /// Given a propagated literal, returns a clause reference of the clause that propagates the
    /// literal. In case the literal was propagated by a clause, the propagating clause is
    /// returned. Otherwise, the literal was propagated by a propagator, in which case a new
    /// clause will be constructed based on the explanation given by the propagator.
    ///
    /// Note that information about the reason for propagation of root literals is not properly
    /// kept, so asking about the reason for a root propagation will cause a panic.
    pub(crate) fn get_propagation_clause_reference(
        &mut self,
        propagated_literal: Literal,
    ) -> ClauseReference {
        pumpkin_assert_moderate!(
            !self
                .assignments_propositional
                .is_literal_root_assignment(propagated_literal),
            "Reasons are not kept properly for root propagations."
        );
        pumpkin_assert_moderate!(
            self.assignments_propositional
                .is_literal_assigned_true(propagated_literal),
            "Reason for propagation only makes sense for true literals."
        );

        let constraint_reference = self
            .assignments_propositional
            .get_variable_reason_constraint(propagated_literal.get_propositional_variable());

        // Case 1: the literal was propagated by the clausal propagator
        if constraint_reference.is_clause() {
            
            self
                .clausal_propagator
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
    pub(crate) fn get_conflict_reason_clause_reference(&mut self) -> ClauseReference {
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
                propagator,
                conjunction,
            } => {
                // create the explanation clause
                //  allocate a fresh vector each time might be a performance bottleneck
                //  todo better ways
                let explanation_literals: Vec<Literal> = conjunction
                    .iter()
                    .map(|&predicate| match predicate {
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
                    })
                    .collect();

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
        let propagation_context =
            PropagationContext::new(self.assignments_integer, self.assignments_propositional);
        let propagator = self.reason_store.get_propagator(reason_ref);
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
