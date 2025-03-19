#![cfg(any(test, doc))]
//! This module exposes helpers that aid testing of CP propagators. The [`TestSolver`] allows
//! setting up specific scenarios under which to test the various operations of a propagator.
use std::fmt::Debug;
use std::fmt::Formatter;

use super::cp::VariableLiteralMappings;
use super::cp::WatchListPropositional;
use super::sat::ClausalPropagator;
use super::sat::ClauseAllocator;
use super::DebugHelper;
use crate::basic_types::ConflictInfo;
use crate::basic_types::Inconsistency;
use crate::basic_types::KeyedVec;
use crate::basic_types::PropagationStatusCP;
use crate::basic_types::PropositionalConjunction;
use crate::engine::cp::propagation::PropagationContext;
use crate::engine::cp::propagation::PropagationContextMut;
use crate::engine::cp::propagation::Propagator;
use crate::engine::cp::propagation::PropagatorId;
use crate::engine::cp::propagation::PropagatorInitialisationContext;
use crate::engine::cp::reason::ReasonStore;
use crate::engine::cp::AssignmentsInteger;
use crate::engine::cp::EmptyDomain;
use crate::engine::cp::WatchListCP;
use crate::engine::predicates::integer_predicate::IntegerPredicate;
use crate::engine::sat::AssignmentsPropositional;
use crate::engine::variables::DomainId;
use crate::engine::variables::IntegerVariable;
use crate::engine::variables::Literal;
use crate::munchkin_assert_simple;
use crate::termination::Indefinite;
use crate::ConstraintOperationError;

/// A container for CP variables, which can be used to test propagators.
#[derive(Debug)]
pub(crate) struct TestSolver {
    pub(crate) assignments_integer: AssignmentsInteger,
    pub(crate) reason_store: ReasonStore,
    pub(crate) assignments_propositional: AssignmentsPropositional,
    pub(crate) watch_list: WatchListCP,
    pub(crate) watch_list_propositional: WatchListPropositional,
    pub(crate) variable_literal_mappings: VariableLiteralMappings,
    pub(crate) clausal_propagator: ClausalPropagator,
    pub(crate) clause_allocator: ClauseAllocator,
    next_id: u32,

    propagators: KeyedVec<PropagatorId, Box<dyn Propagator>>,
}

impl Default for TestSolver {
    fn default() -> Self {
        let mut result = Self {
            assignments_integer: Default::default(),
            reason_store: Default::default(),
            assignments_propositional: Default::default(),
            watch_list: Default::default(),
            watch_list_propositional: Default::default(),
            variable_literal_mappings: Default::default(),
            clausal_propagator: Default::default(),
            clause_allocator: Default::default(),
            next_id: Default::default(),
            propagators: Default::default(),
        };
        let true_literal = Literal::new(
            result
                .variable_literal_mappings
                .create_new_propositional_variable(
                    &mut result.watch_list_propositional,
                    &mut result.clausal_propagator,
                    &mut result.assignments_propositional,
                ),
            true,
        );
        result.assignments_propositional.true_literal = true_literal;
        result.assignments_propositional.false_literal = !true_literal;

        let addition = result.add_clause(vec![true_literal]);
        assert!(addition.is_ok());

        result
    }
}

type BoxedPropagator = Box<dyn Propagator>;

impl Debug for BoxedPropagator {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "test_helper::Propagator(<boxed value>)")
    }
}

#[allow(unused, reason = "can be used in an assignment")]
impl TestSolver {
    pub(crate) fn set_decision(&mut self, literal: Literal) {
        self.assignments_propositional
            .enqueue_decision_literal(literal)
    }

    pub(crate) fn propagate_clausal_propagator(&mut self) -> Result<(), ConflictInfo> {
        self.clausal_propagator.propagate(
            &mut self.assignments_propositional,
            &mut self.clause_allocator,
        )
    }

    pub(crate) fn add_clause(
        &mut self,
        literals: Vec<Literal>,
    ) -> Result<(), ConstraintOperationError> {
        self.clausal_propagator.add_permanent_clause(
            literals,
            &mut self.assignments_propositional,
            &mut self.clause_allocator,
        )
    }

    pub(crate) fn increase_decision_level(&mut self) {
        self.assignments_integer.increase_decision_level();
        self.assignments_propositional.increase_decision_level();
    }

    pub(crate) fn new_variable(&mut self, lb: i32, ub: i32) -> DomainId {
        self.variable_literal_mappings.create_new_domain(
            lb,
            ub,
            &mut self.assignments_integer,
            &mut self.watch_list,
            &mut self.watch_list_propositional,
            &mut self.clausal_propagator,
            &mut self.assignments_propositional,
            &mut self.clause_allocator,
        )
    }

    pub(crate) fn new_sparse_variable(&mut self, values: &[i32]) -> DomainId {
        assert!(
            !values.is_empty(),
            "cannot create a variable with an empty domain"
        );
        let mut values = values.to_vec();

        values.sort();
        values.dedup();

        let lower_bound = values[0];
        let upper_bound = values[values.len() - 1];

        let domain_id = self.new_variable(lower_bound, upper_bound);

        let mut next_idx = 0;
        for value in lower_bound..=upper_bound {
            if value == values[next_idx] {
                next_idx += 1;
            } else {
                self.assignments_integer
                    .remove_initial_value_from_domain(domain_id, value, None)
                    .expect("the domain should not be empty");
                self.assignments_propositional.enqueue_decision_literal(
                    self.variable_literal_mappings.get_inequality_literal(
                        domain_id,
                        value,
                        &self.assignments_propositional,
                        &self.assignments_integer,
                    ),
                )
            }
        }
        munchkin_assert_simple!(
            next_idx == values.len(),
            "Expected all values to have been processed"
        );

        domain_id
    }

    pub(crate) fn new_literal(&mut self) -> Literal {
        let variable = self
            .variable_literal_mappings
            .create_new_propositional_variable(
                &mut self.watch_list_propositional,
                &mut self.clausal_propagator,
                &mut self.assignments_propositional,
            );

        Literal::new(variable, true)
    }

    pub(crate) fn new_propagator(
        &mut self,
        propagator: impl Propagator + 'static,
    ) -> Result<PropagatorId, Inconsistency> {
        let id = PropagatorId(self.next_id);
        self.next_id += 1;

        let mut propagator: Box<dyn Propagator> = Box::new(propagator);

        propagator
            .initialise_at_root(&mut PropagatorInitialisationContext::new(
                &mut self.watch_list,
                &mut self.watch_list_propositional,
                id,
                &self.assignments_integer,
                &self.assignments_propositional,
                true,
                true,
            ))
            .expect("do not detect conflicts in initialise at root");

        let num_trail_entries_before = self.assignments_integer.num_trail_entries();

        self.propagators.push(propagator);

        self.propagate(id)?;

        Ok(id)
    }

    pub(crate) fn assert_domain<Var: IntegerVariable>(&self, var: Var, domain: Vec<i32>) {
        if domain.is_empty() {
            panic!("Domain provided to test solver is empty");
        }
        let min_domain = *domain.iter().min().unwrap();
        let max_domain = *domain.iter().max().unwrap();

        self.assert_bounds(var.clone(), min_domain, max_domain);
        for value in min_domain..=max_domain {
            if !domain.contains(&value) {
                assert!(
                    !self.contains(var.clone(), value),
                    "{value} was in the domain while it should not be (provided domain {domain:?})"
                )
            } else {
                assert!(
                    self.contains(var.clone(), value),
                    "{value} was not in the domain while it should be (provided domain {domain:?})"
                )
            }
        }
    }

    pub(crate) fn contains<Var: IntegerVariable>(&self, var: Var, value: i32) -> bool {
        var.contains(&self.assignments_integer, value)
    }

    pub(crate) fn lower_bound(&self, var: DomainId) -> i32 {
        self.assignments_integer.get_lower_bound(var)
    }

    pub(crate) fn increase_lower_bound(&mut self, var: DomainId, value: i32) {
        let result = self
            .assignments_integer
            .tighten_lower_bound(var, value, None);
        assert!(result.is_ok(), "The provided value to `increase_lower_bound` caused an empty domain, generally the propagator should not be notified of this change!");
    }

    pub(crate) fn set_literal(&mut self, var: Literal, val: bool) {
        self.assignments_propositional
            .enqueue_decision_literal(if val { var } else { !var });
    }

    pub(crate) fn is_literal_false(&self, var: Literal) -> bool {
        self.assignments_propositional
            .is_literal_assigned_false(var)
    }

    pub(crate) fn upper_bound(&self, var: DomainId) -> i32 {
        self.assignments_integer.get_upper_bound(var)
    }

    pub(crate) fn remove(&mut self, var: DomainId, value: i32) -> Result<(), EmptyDomain> {
        self.assignments_integer
            .remove_value_from_domain(var, value, None)
    }

    pub(crate) fn propagate(&mut self, propagator: PropagatorId) -> PropagationStatusCP {
        let num_trail_entries_before = self.assignments_integer.num_trail_entries();
        let context = PropagationContextMut::new(
            &mut self.assignments_integer,
            &mut self.reason_store,
            &mut self.assignments_propositional,
            PropagatorId(0),
            true,
            true,
        );
        let propagate = self.propagators[propagator].propagate(context);

        assert!(
            DebugHelper::debug_check_propagations(
                &mut Indefinite,
                num_trail_entries_before,
                propagator,
                &self.assignments_integer,
                &self.assignments_propositional,
                &self.variable_literal_mappings,
                &mut self.reason_store,
                &self.propagators,
                true,
                true
            ),
            "Inconsistency in explanation detected in test case"
        );
        propagate
    }

    pub(crate) fn get_reason_int(
        &mut self,
        predicate: IntegerPredicate,
    ) -> &PropositionalConjunction {
        let reason_ref = self.assignments_integer.get_reason_for_predicate(predicate);
        let context = PropagationContext::new(
            &self.assignments_integer,
            &self.assignments_propositional,
            true,
            true,
        );
        self.reason_store
            .get_or_compute(reason_ref, &context)
            .expect("reason_ref should not be stale")
    }

    pub(crate) fn get_reason_bool(
        &mut self,
        literal: Literal,
        assignment: bool,
    ) -> &PropositionalConjunction {
        let reason_ref = self
            .assignments_propositional
            .get_reason_for_assignment(literal, assignment);
        let context = PropagationContext::new(
            &self.assignments_integer,
            &self.assignments_propositional,
            true,
            true,
        );
        self.reason_store
            .get_or_compute(reason_ref, &context)
            .expect("reason_ref should not be stale")
    }

    pub(crate) fn assert_bounds<Var: IntegerVariable>(&self, var: Var, lb: i32, ub: i32) {
        let actual_lb = var.lower_bound(&self.assignments_integer);
        let actual_ub = var.upper_bound(&self.assignments_integer);

        assert_eq!(
            (lb, ub), (actual_lb, actual_ub),
            "The expected bounds [{lb}..{ub}] did not match the actual bounds [{actual_lb}..{actual_ub}]"
        );
    }
}
