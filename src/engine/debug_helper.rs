use std::fmt::Debug;
use std::fmt::Formatter;

#[cfg(any(feature = "explanation-checks", test))]
use log::debug;
use log::warn;

#[cfg(any(feature = "explanation-checks", test))]
use super::cp::propagation::PropagationContext;
#[cfg(any(feature = "explanation-checks", test))]
use super::cp::reason::ReasonStore;
#[cfg(any(feature = "explanation-checks", test))]
use super::predicates::integer_predicate::IntegerPredicate;
#[cfg(any(feature = "explanation-checks", test))]
use super::predicates::integer_predicate::IntegerPredicateConversionError;
use super::sat::ClauseAllocator;
#[cfg(any(feature = "explanation-checks", test))]
use super::termination::TerminationCondition;
#[cfg(any(feature = "explanation-checks", test))]
use crate::basic_types::HashSet;
use crate::basic_types::KeyedVec;
#[cfg(any(feature = "explanation-checks", test))]
use crate::basic_types::PropositionalConjunction;
use crate::engine::cp::propagation::PropagationContextMut;
use crate::engine::cp::propagation::Propagator;
use crate::engine::cp::propagation::PropagatorId;
use crate::engine::cp::AssignmentsInteger;
#[cfg(any(feature = "explanation-checks", test))]
use crate::engine::cp::VariableLiteralMappings;
#[cfg(any(feature = "explanation-checks", test))]
use crate::engine::predicates::predicate::Predicate;
use crate::engine::sat::AssignmentsPropositional;
use crate::engine::sat::ClausalPropagator;
use crate::munchkin_assert_simple;
#[cfg(any(feature = "explanation-checks", test))]
use crate::predicates::PredicateConstructor;

#[derive(Copy, Clone)]
pub(crate) struct DebugDyn<'a> {
    trait_name: &'a str,
}

impl<'a> DebugDyn<'a> {
    pub(crate) fn from(trait_name: &'a str) -> Self {
        DebugDyn { trait_name }
    }
}

impl Debug for DebugDyn<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "<dyn {}>", self.trait_name)
    }
}

#[derive(Debug, Copy, Clone)]
pub(crate) struct DebugHelper {}

impl DebugHelper {
    // this method is only to be called after the solver completed propagation until a fixed point
    // and no conflict were detected  the point is to check whether there is a propagation that
    // missed a propagation or failure  additionally checks whether the internal data structures
    // of the clausal propagator are okay and consistent with the assignments_propositional
    pub(crate) fn debug_fixed_point_propagation(
        clausal_propagator: &ClausalPropagator,
        assignments_integer: &AssignmentsInteger,
        assignments_propositional: &AssignmentsPropositional,
        clause_allocator: &ClauseAllocator,
        propagators_cp: &KeyedVec<PropagatorId, Box<dyn Propagator>>,
        use_non_generic_conflict_explanation: bool,
        use_non_generic_propagation_explanation: bool,
    ) -> bool {
        let mut assignments_integer_clone = assignments_integer.clone();
        let mut assignments_propostional_clone = assignments_propositional.clone();
        // check whether constraint programming propagators missed anything
        //  ask each propagator to propagate from scratch, and check whether any new propagations
        // took place  if a new propagation took place, then the main propagation loop
        // missed at least one propagation, indicating buggy behaviour  two notes:
        //      1. it could still be that the main propagation loop propagates more than it should
        //         however this will not be detected with this debug check instead such behaviour
        //         may be detected when debug-checking the reason for propagation
        //      2. we assume fixed-point propagation, it could be in the future that this may change
        //  todo expand the output given by the debug check
        for (propagator_id, propagator) in propagators_cp.iter().enumerate() {
            let num_entries_on_trail_before_propagation =
                assignments_integer_clone.num_trail_entries();
            let num_entries_on_propositional_trail_before_propagation =
                assignments_propostional_clone.num_trail_entries();

            let mut reason_store = Default::default();
            let context = PropagationContextMut::new(
                &mut assignments_integer_clone,
                &mut reason_store,
                &mut assignments_propostional_clone,
                PropagatorId(propagator_id.try_into().unwrap()),
                use_non_generic_conflict_explanation,
                use_non_generic_propagation_explanation,
            );
            let propagation_status_cp = propagator.propagate(context);

            if let Err(ref failure_reason) = propagation_status_cp {
                warn!(
                    "Propagator '{}' with id '{propagator_id}' seems to have missed a conflict in its regular propagation algorithms!
                     Aborting!\n
                     Expected reason: {failure_reason:?}", propagator.name()
                );
                panic!();
            }

            let num_missed_propagations = assignments_integer_clone.num_trail_entries()
                - num_entries_on_trail_before_propagation;

            let num_missed_propositional_propagations = assignments_propostional_clone
                .num_trail_entries()
                - num_entries_on_propositional_trail_before_propagation;

            if num_missed_propagations > 0 {
                eprintln!(
                    "Propagator '{}' with id '{propagator_id}' missed predicates:",
                    propagator.name(),
                );

                for idx in num_entries_on_trail_before_propagation
                    ..assignments_integer_clone.num_trail_entries()
                {
                    let trail_entry = assignments_integer_clone.get_trail_entry(idx);
                    let pred = trail_entry.predicate;
                    eprintln!("  - {pred:?}");
                }

                panic!("missed propagations");
            }
            if num_missed_propositional_propagations > 0 {
                panic!("Missed propositional propagations");
            }
        }
        // then check the clausal propagator
        munchkin_assert_simple!(
            clausal_propagator.debug_check_state(assignments_propositional, clause_allocator)
        );
        true
    }

    #[allow(
        clippy::too_many_arguments,
        reason = "Should be refactored in the future"
    )]
    #[cfg(feature = "explanation-checks")]
    pub(crate) fn debug_reported_failure(
        assignments_integer: &AssignmentsInteger,
        assignments_propositional: &AssignmentsPropositional,
        variable_literal_mappings: &VariableLiteralMappings,
        failure_reason: &PropositionalConjunction,
        propagator: &dyn Propagator,
        propagator_id: PropagatorId,
        use_non_generic_conflict_explanation: bool,
        use_non_generic_propagation_explanation: bool,
    ) {
        let name = propagator.name();
        if name == "LinearLeq" || name == "Reified(LinearLeq)" {
            // We do not check the explanations of the linear less than or equal propagator or
            // reified linear less than or equals for efficiency
            return;
        }
        DebugHelper::debug_reported_propagations_reproduce_failure(
            assignments_integer,
            assignments_propositional,
            variable_literal_mappings,
            failure_reason,
            propagator,
            propagator_id,
            use_non_generic_conflict_explanation,
            use_non_generic_propagation_explanation,
        )
    }

    #[allow(
        clippy::too_many_arguments,
        reason = "Should be refactored in the future"
    )]
    #[cfg(feature = "explanation-checks")]
    fn debug_reported_propagations_reproduce_failure(
        assignments_integer: &AssignmentsInteger,
        assignments_propositional: &AssignmentsPropositional,
        variable_literal_mappings: &VariableLiteralMappings,
        failure_reason: &PropositionalConjunction,
        propagator: &dyn Propagator,
        propagator_id: PropagatorId,
        use_non_generic_conflict_explanation: bool,
        use_non_generic_propagation_explanation: bool,
    ) {
        let mut assignments_integer_clone = assignments_integer.debug_create_empty_clone();
        let mut assignments_propositional_clone =
            assignments_propositional.debug_create_empty_clone();

        let reason_predicates: Vec<Predicate> = failure_reason.iter().copied().collect();
        let adding_predicates_was_successful =
            DebugHelper::debug_add_predicates_to_assignment_integers(
                &mut assignments_integer_clone,
                &reason_predicates,
            );
        let adding_propositional_predicates_was_successful =
            DebugHelper::debug_add_predicates_to_assignment_propositional(
                &assignments_integer_clone,
                &mut assignments_propositional_clone,
                variable_literal_mappings,
                &reason_predicates,
            );

        if adding_predicates_was_successful && adding_propositional_predicates_was_successful {
            //  now propagate using the debug propagation method
            let mut reason_store = Default::default();
            let context = PropagationContextMut::new(
                &mut assignments_integer_clone,
                &mut reason_store,
                &mut assignments_propositional_clone,
                propagator_id,
                use_non_generic_conflict_explanation,
                use_non_generic_propagation_explanation,
            );
            let debug_propagation_status_cp = propagator.propagate(context);
            if debug_propagation_status_cp.is_ok()
                && Self::is_circuit_explanation_with_only_inequalities(
                    propagator,
                    &reason_predicates,
                )
            {
                Self::debug_circuit_reason_conflict(
                    &reason_predicates,
                    assignments_integer,
                    assignments_propositional,
                    variable_literal_mappings,
                    propagator,
                    propagator_id,
                    use_non_generic_conflict_explanation,
                    use_non_generic_propagation_explanation,
                );
            } else {
                assert!(
                    debug_propagation_status_cp.is_err(),
                    "Debug propagation could not reproduce the conflict reported
                 by the propagator '{}' with id '{propagator_id}'.\n
                 The reported failure: {failure_reason}",
                    propagator.name()
                );
            }
        } else {
            // if even adding the predicates failed, the method adding the predicates would have
            // printed debug info already  so we just need to add more information to
            // indicate where the failure happened
            panic!(
                "Bug detected for '{}' propagator with id '{propagator_id}' after a failure reason
                 was given by the propagator.",
                propagator.name()
            );
        }
    }

    /// Checks whether the propagations of the propagator since `num_trail_entries_before` are
    /// reproducible by performing 1 check:
    /// 1. Setting the reason for a propagation should lead to the same propagation when debug
    ///    propagating from scratch
    ///
    /// Note that this method does not check whether an empty explanation is correct!
    #[allow(
        clippy::too_many_arguments,
        reason = "Should be refactored in the future"
    )]
    #[cfg(any(feature = "explanation-checks", test))]
    pub(crate) fn debug_check_propagations(
        termination: &mut impl TerminationCondition,
        num_trail_entries_before: usize,
        propagator_id: PropagatorId,
        assignments: &AssignmentsInteger,
        assignments_propositional: &AssignmentsPropositional,
        variable_literal_mappings: &VariableLiteralMappings,
        reason_store: &mut ReasonStore,
        propagators_cp: &KeyedVec<PropagatorId, Box<dyn Propagator>>,
        use_non_generic_conflict_explanation: bool,
        use_non_generic_propagation_explanation: bool,
    ) -> bool {
        let name = propagators_cp[propagator_id].name();
        if name == "LinearLeq" || name == "Reified(LinearLeq)" {
            // We do not check the explanations of the linear less than or equal propagator or
            // reified linear less than or equals for efficiency
            return true;
        }
        let mut result = true;
        for trail_index in num_trail_entries_before..assignments.num_trail_entries() {
            if termination.should_stop() {
                return true;
            }
            let trail_entry = assignments.get_trail_entry(trail_index);

            let reason = reason_store
                .get_or_compute(
                    trail_entry
                        .reason
                        .expect("Expected checked propagation to have a reason"),
                    &PropagationContext::new(
                        assignments,
                        assignments_propositional,
                        use_non_generic_conflict_explanation,
                        use_non_generic_propagation_explanation,
                    ),
                )
                .expect("Expected reason to exist for integer trail entry");

            if reason.is_empty() {
                continue;
            }

            result &= Self::debug_propagator_reason(
                trail_entry.predicate,
                reason,
                assignments,
                assignments_propositional,
                variable_literal_mappings,
                propagators_cp[propagator_id].as_ref(),
                propagator_id,
                use_non_generic_conflict_explanation,
                use_non_generic_propagation_explanation,
            );
        }
        result
    }

    #[allow(
        clippy::too_many_arguments,
        reason = "Should be refactored in the future"
    )]
    #[cfg(any(feature = "explanation-checks", test))]
    fn debug_propagator_reason(
        propagated_predicate: IntegerPredicate,
        reason: &PropositionalConjunction,
        assignments_integer: &AssignmentsInteger,
        assignments_propositional: &AssignmentsPropositional,
        variable_literal_mappings: &VariableLiteralMappings,
        propagator: &dyn Propagator,
        propagator_id: PropagatorId,
        use_non_generic_conflict_explanation: bool,
        use_non_generic_propagation_explanation: bool,
    ) -> bool {
        assert!(
            reason.iter().all(|predicate| {
                if let Ok(integer_predicate) = (*predicate).try_into() {
                    assignments_integer.does_integer_predicate_hold(integer_predicate)
                } else {
                    true
                }
            }),
            "Found propagation with predicates which do not hold - Propagator: {}",
            propagator.name()
        );
        // Note that it could be the case that the reason contains the trivially false predicate in
        // case of lifting!
        //
        // Also note that the reason could contain the integer variable whose domain is propagated
        // itself

        // Check #1
        // Does setting the predicates from the reason indeed lead to the propagation?
        {
            let mut assignments_clone = assignments_integer.debug_create_empty_clone();
            let mut assignments_propositional_clone =
                assignments_propositional.debug_create_empty_clone();

            let reason_predicates: Vec<Predicate> = reason.iter().copied().collect();
            let adding_predicates_was_successful =
                DebugHelper::debug_add_predicates_to_assignment_integers(
                    &mut assignments_clone,
                    &reason_predicates,
                );
            let adding_literals_was_successful =
                DebugHelper::debug_add_predicates_to_assignment_propositional(
                    &assignments_clone,
                    &mut assignments_propositional_clone,
                    variable_literal_mappings,
                    &reason_predicates,
                );
            if adding_predicates_was_successful && adding_literals_was_successful {
                // Now propagate using the debug propagation method.
                let mut reason_store = Default::default();
                let context = PropagationContextMut::new(
                    &mut assignments_clone,
                    &mut reason_store,
                    &mut assignments_propositional_clone,
                    propagator_id,
                    use_non_generic_conflict_explanation,
                    use_non_generic_propagation_explanation,
                );
                let debug_propagation_status_cp = propagator.propagate(context);

                // Note that it could be the case that the propagation leads to conflict, in this
                // case it should be the result of a propagation (i.e. an EmptyDomain)
                if let Err(_conflict) = debug_propagation_status_cp {
                    // If we have found an error then it should either be derived by an empty
                    // domain due to the same propagation holding
                    //
                    // or
                    //
                    // The conflict explanation should be a subset of the reason literals for the
                    // propagation or all of the reason literals should be in the conflict
                    // explanation

                    // For now we do not check anything here since the check  could be erroneous
                } else {
                    let result =
                        assignments_clone.does_integer_predicate_hold(propagated_predicate);
                    if !result
                        && Self::is_circuit_explanation_with_only_inequalities(
                            propagator,
                            &reason_predicates,
                        )
                    {
                        Self::debug_circuit_reason_propagation(
                            propagated_predicate,
                            &reason_predicates,
                            assignments_integer,
                            assignments_propositional,
                            variable_literal_mappings,
                            propagator,
                            propagator_id,
                            use_non_generic_conflict_explanation,
                            use_non_generic_propagation_explanation,
                        );
                    } else {
                        // The predicate was either a propagation for the assignments_integer or
                        // assignments_propositional

                        assert!(
                    assignments_clone.does_integer_predicate_hold(propagated_predicate),
                    "Debug propagation could not obtain the propagated predicate given the provided reason.\n
                     Propagator: '{}'\n
                     Propagator id: {propagator_id}\n
                     Reported reason: {reason:?}\n
                     Reported propagation: {propagated_predicate}",
                    propagator.name()
                );
                    }
                }
            } else {
                // Adding the predicates of the reason to the assignments led to failure
                panic!(
                    "Bug detected for '{}' propagator with id '{propagator_id}'
                     after a reason was given by the propagator. This could indicate that the reason contained conflicting predicates.",
                    propagator.name()
                );
            }
        }

        true
    }

    #[cfg(any(feature = "explanation-checks", test))]
    fn is_circuit_explanation_with_only_inequalities(
        propagator: &dyn Propagator,
        original_reason: &[Predicate],
    ) -> bool {
        propagator.name().contains("Circuit")
            && original_reason.iter().all(|predicate| {
                let integer_predicate: Result<IntegerPredicate, IntegerPredicateConversionError> =
                    (*predicate).try_into();
                if let Ok(predicate) = integer_predicate {
                    predicate.is_not_equal_predicate()
                } else {
                    false
                }
            })
    }

    #[cfg(any(feature = "explanation-checks", test))]
    fn transform_circuit_reason(
        original_reason: &[Predicate],
        assignments_integer: &AssignmentsInteger,
    ) -> Vec<Predicate> {
        let mut variables = HashSet::new();
        original_reason.iter().for_each(|&predicate| {
            let _ = variables.insert(predicate.get_domain().unwrap());
        });

        variables
            .iter()
            .map(|&domain_id| -> _ {
                domain_id.equality_predicate(assignments_integer.get_assigned_value(domain_id))
            })
            .collect::<Vec<_>>()
    }

    #[cfg(feature = "explanation-checks")]
    fn debug_circuit_reason_conflict(
        original_reason: &[Predicate],
        assignments_integer: &AssignmentsInteger,
        assignments_propositional: &AssignmentsPropositional,
        variable_literal_mappings: &VariableLiteralMappings,
        propagator: &dyn Propagator,
        propagator_id: PropagatorId,
        use_non_generic_conflict_explanation: bool,
        use_non_generic_propagation_explanation: bool,
    ) {
        // Special case for the circuit propagator
        let reason_predicates =
            Self::transform_circuit_reason(original_reason, assignments_integer);
        let mut assignments_integer_clone = assignments_integer.debug_create_empty_clone();
        let mut assignments_propositional_clone =
            assignments_propositional.debug_create_empty_clone();

        let adding_predicates_was_successful =
            DebugHelper::debug_add_predicates_to_assignment_integers(
                &mut assignments_integer_clone,
                &reason_predicates,
            );
        let adding_propositional_predicates_was_successful =
            DebugHelper::debug_add_predicates_to_assignment_propositional(
                &assignments_integer_clone,
                &mut assignments_propositional_clone,
                variable_literal_mappings,
                &reason_predicates,
            );

        if adding_predicates_was_successful && adding_propositional_predicates_was_successful {
            //  now propagate using the debug propagation method
            let mut reason_store = Default::default();
            let context = PropagationContextMut::new(
                &mut assignments_integer_clone,
                &mut reason_store,
                &mut assignments_propositional_clone,
                propagator_id,
                use_non_generic_conflict_explanation,
                use_non_generic_propagation_explanation,
            );
            let debug_propagation_status_cp = propagator.propagate(context);
            assert!(
                debug_propagation_status_cp.is_err(),
                "Debug propagation could not reproduce the conflict reported
                 by the propagator '{}' with id '{propagator_id}'.\n
                 The reported failure: {original_reason:?}",
                propagator.name()
            );
        } else {
            // if even adding the predicates failed, the method adding the predicates would have
            // printed debug info already  so we just need to add more information to
            // indicate where the failure happened
            panic!(
                "Bug detected for '{}' propagator with id '{propagator_id}' after a failure reason
                 was given by the propagator.",
                propagator.name()
            );
        }
    }

    #[cfg(any(feature = "explanation-checks", test))]
    #[allow(
        clippy::too_many_arguments,
        reason = "Should be refactored in the future"
    )]
    fn debug_circuit_reason_propagation(
        propagated_predicate: IntegerPredicate,
        original_reason: &[Predicate],
        assignments_integer: &AssignmentsInteger,
        assignments_propositional: &AssignmentsPropositional,
        variable_literal_mappings: &VariableLiteralMappings,
        propagator: &dyn Propagator,
        propagator_id: PropagatorId,
        use_non_generic_conflict_explanation: bool,
        use_non_generic_propagation_explanation: bool,
    ) {
        // Special case for the circuit propagator
        let reason_predicates =
            Self::transform_circuit_reason(original_reason, assignments_integer);

        let mut assignments_clone = assignments_integer.debug_create_empty_clone();
        let mut assignments_propositional_clone =
            assignments_propositional.debug_create_empty_clone();
        let adding_predicates_was_successful =
            DebugHelper::debug_add_predicates_to_assignment_integers(
                &mut assignments_clone,
                &reason_predicates,
            );
        let adding_literals_was_successful =
            DebugHelper::debug_add_predicates_to_assignment_propositional(
                &assignments_clone,
                &mut assignments_propositional_clone,
                variable_literal_mappings,
                &reason_predicates,
            );
        if adding_predicates_was_successful && adding_literals_was_successful {
            // Now propagate using the debug propagation method.
            let mut reason_store = Default::default();
            let context = PropagationContextMut::new(
                &mut assignments_clone,
                &mut reason_store,
                &mut assignments_propositional_clone,
                propagator_id,
                use_non_generic_conflict_explanation,
                use_non_generic_propagation_explanation,
            );
            let debug_propagation_status_cp = propagator.propagate(context);
            if let Err(_conflict) = debug_propagation_status_cp {
                // If we have found an error then it should either be derived by an
                // empty domain due to the same
                // propagation holding
                //
                // or
                //
                // The conflict explanation should be a subset of the reason
                // literals for the propagation or
                // all of the reason literals should be in the conflict
                // explanation

                // For now we do not check anything here since the check  could be
                // erroneous
            } else {
                assert!(
                    assignments_clone.does_integer_predicate_hold(propagated_predicate),
                    "Debug propagation could not obtain the propagated predicate given the provided reason.\n
                     Propagator: '{}'\n
                     Propagator id: {propagator_id}\n
                     Reported reason: {reason_predicates:?}\n
                     Reported propagation: {propagated_predicate}",
                    propagator.name()
                );
            }
        } else {
            // Adding the predicates of the reason to the assignments led to failure
            panic!(
                    "Bug detected for '{}' propagator with id '{propagator_id}'
                     after a reason was given by the propagator. This could indicate that the reason contained conflicting predicates.",
                    propagator.name()
                );
        }
    }
}

// methods that serve as small utility functions
impl DebugHelper {
    #[cfg(any(feature = "explanation-checks", test))]
    fn debug_add_predicates_to_assignment_integers(
        assignments_integer: &mut AssignmentsInteger,
        predicates: &[Predicate],
    ) -> bool {
        for predicate in predicates {
            if let Ok(integer_predicate) =
                <Predicate as TryInto<IntegerPredicate>>::try_into(*predicate)
            {
                let outcome = assignments_integer.apply_integer_predicate(integer_predicate, None);
                match outcome {
                    Ok(()) => {
                        // do nothing, everything is okay
                    }
                    Err(_) => {
                        // trivial failure, this is unexpected
                        //  e.g., this can happen if the propagator reported [x >= a] and [x <= a-1]
                        debug!(
                            "Trivial failure detected in the given reason.\n
                         The reported failure: {predicate}\n
                         Failure detected after trying to apply '{predicate}'.",
                        );
                        return false;
                    }
                }
            }
        }
        true
    }

    #[cfg(any(feature = "explanation-checks", test))]
    fn debug_add_predicates_to_assignment_propositional(
        assignments_integer: &AssignmentsInteger,
        assignments_propositional: &mut AssignmentsPropositional,
        variable_literal_mappings: &VariableLiteralMappings,
        predicates: &[Predicate],
    ) -> bool {
        for predicate in predicates {
            let literal = if let Ok(integer_predicate) =
                <Predicate as TryInto<IntegerPredicate>>::try_into(*predicate)
            {
                variable_literal_mappings.get_literal(
                    integer_predicate,
                    assignments_propositional,
                    assignments_integer,
                )
            } else {
                predicate
                    .get_literal_of_bool_predicate(assignments_propositional.true_literal)
                    .unwrap()
            };
            if assignments_propositional.is_literal_assigned_false(literal) {
                debug!(
                    "Trivial failure detected in the given reason.\n
                     The reported failure: {predicate}\n
                     Failure detected after trying to apply '{predicate}'.",
                );
                return false;
            }
            if !assignments_propositional.is_literal_assigned(literal) {
                // It could be the case that the explanation of a failure/propagation contains a
                // predicate which is always true For example, if we have a variable
                // x \in [0..10] and the explanation contains [x >= -1] then this will always
                // evaluate to the true literal However, the true literal is always
                // assigned leading to checks related to this enqueuing failing
                assignments_propositional.enqueue_decision_literal(literal);
            }
        }
        true
    }
}
