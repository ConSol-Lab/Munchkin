//! An API to verify the RP property of clauses.
//!
//! Reverse propagation (RP) is a generalization of Reverse Unit Propagation (RUP). In the latter
//! case, a clause `c` is RUP with respect to a clause database `F` when `¬c ∧ F ⟹ false` and this
//! conflict can be detected through clausal (aka unit) propagation.
//! RP generalizes this property by dropping the requirement for `F` to be a
//! database of clauses. It can be a database of any constraint type.
//!
//! This concept is mostly useful when dealing with clausal proofs. In particular, the DRCP format,
//! which is the format used by Pumpkin to proofs when solving a CP problem.
//!
//! Since validating the RP property of a clause of predicates requires a CP propagation engine,
//! and given that Pumpkin implements such an engine, the [`RpEngine`] exposes an API to verify the
//! RP property of clauses.

use std::num::NonZero;

use log::warn;

use crate::basic_types::ClauseReference;
use crate::basic_types::HashMap;
use crate::basic_types::HashSet;
use crate::basic_types::StoredConflictInfo;
use crate::branching::Brancher;
use crate::branching::SelectionContext;
use crate::engine::cp::propagation::PropagationContext;
use crate::engine::predicates::predicate::Predicate;
use crate::engine::variables::Literal;
use crate::engine::ConstraintSatisfactionSolver;
use crate::proof::inference_labels;
use crate::termination::Indefinite;
use crate::Solver;

/// An API for performing backwards reverse propagation of a clausal proof. The API allows the
/// reasons for all propagations that are used to derive the RP clause to be accessed.
///
/// To use the RpEngine, one can do the following:
/// 1. Initialise it with a base model against which the individual reverse propagating clauses will
///    be checked.
/// 2. Add reverse propagating clauses through [`RpEngine::add_rp_clause`]. The order in which this
///    happens matters.
/// 3. Check whether a propagation can derive a conflict under certain assumptions (probably the
///    negation of a reverse propagating clause which is no-longer in the engine).
/// 4. Remove the reverse propagating clauses with [`RpEngine::remove_last_rp_clause`] in reverse
///    order in which they were added.
#[derive(Debug)]
pub(crate) struct RpEngine {
    pub(crate) solver: ConstraintSatisfactionSolver,
    rp_clauses: Vec<(RpClause, Vec<Literal>)>,
    rp_unit_clauses: HashMap<Literal, RpClauseHandle>,
    rp_allocated_clauses: HashMap<ClauseReference, RpClauseHandle>,
}

/// A handle to a reverse propagating clause. These clauses are added to the [`RpEngine`] through
/// [`RpEngine::add_rp_clause`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct RpClauseHandle(usize);

/// One of the reasons contributing to unsatisfiability when calling
/// [`RpEngine::propagate_under_assumptions`].
#[derive(Debug, Clone)]
pub(crate) enum ConflictReason {
    Clause(RpClauseHandle),
    Propagator {
        premises: Vec<Literal>,
        propagated: Option<Literal>,
        tag: NonZero<u32>,
        label: &'static str,
    },
}

/// The reason for a conflict is a list of [`ConflictReason`]s.
pub(crate) type ReversePropagationConflict = Vec<ConflictReason>;

impl RpEngine {
    /// Create a new reverse propagating engine based on a [`Solver`] initialized with the model of
    /// the problem.
    pub(crate) fn new(solver: Solver) -> Self {
        RpEngine {
            solver: solver.into_satisfaction_solver(),
            rp_clauses: vec![],
            rp_unit_clauses: HashMap::default(),
            rp_allocated_clauses: HashMap::default(),
        }
    }

    /// Add a new reverse propagating clause to the engine. The clause should not be empty, and
    /// the engine should not be in an conflicting state.
    ///
    /// If the new clause causes a conflict under propagation, the engine will be in a conflicting
    /// state. A call to [`RpEngine::remove_last_rp_clause`] will remove the newly added clause and
    /// reset the engine to a useable state.
    pub(crate) fn add_rp_clause(
        &mut self,
        clause: impl IntoIterator<Item = Literal>,
    ) -> Result<RpClauseHandle, (RpClauseHandle, ReversePropagationConflict)> {
        let input_clause: Vec<Literal> = clause.into_iter().collect();

        let filtered_clause: Vec<Literal> = input_clause
            .iter()
            .copied()
            .filter(|literal| self.solver.get_literal_value(*literal).is_none())
            .collect();

        assert!(!filtered_clause.is_empty(), "cannot add the empty clause");

        let new_handle = RpClauseHandle(self.rp_clauses.len());
        println!("len = {:?}", filtered_clause.len());

        if filtered_clause.len() == 1 {
            self.rp_clauses
                .push((RpClause::Unit(filtered_clause[0]), input_clause));
            // todo remove, rp_unit clauses
            let _ = self.rp_unit_clauses.insert(filtered_clause[0], new_handle);

            self.solver.declare_new_decision_level();
            self.enqueue_and_propagate(filtered_clause[0])
                .map_err(|e| (new_handle, e))?;
        } else {
            let propagating_literal = self.get_propagating_literal(&filtered_clause);

            let reference = self.solver.add_allocated_deletable_clause(filtered_clause);

            let old_handle = self.rp_allocated_clauses.insert(reference, new_handle);
            assert!(old_handle.is_none());

            self.rp_clauses
                .push((RpClause::ClauseRef(reference), input_clause));

            if let Some(propagating_literal) = propagating_literal {
                self.enqueue_and_propagate(propagating_literal)
                    .map_err(|e| (new_handle, e))?;
            }
        }

        Ok(new_handle)
    }

    fn get_propagating_literal(&mut self, clause: &[Literal]) -> Option<Literal> {
        self.check_assigned_literals(clause);

        let false_count = clause
            .iter()
            .filter(|&&literal| self.solver.get_literal_value(literal) == Some(false))
            .count();

        if false_count == clause.len() - 1 {
            clause
                .iter()
                .find(|&&literal| self.solver.get_literal_value(literal).is_some())
                .copied()
        } else {
            None
        }
    }

    fn check_assigned_literals(&mut self, clause: &[Literal]) {
        if clause
            .iter()
            .any(|&literal| self.solver.get_literal_value(literal).is_some())
        {
            warn!("Adding RP clause with assigned literals.");
        }
    }

    /// Remove the last clause in the proof from consideration and return the literals it contains.
    pub(crate) fn remove_last_rp_clause(&mut self) -> Option<Vec<Literal>> {
        let (last_rp_clause, input_clause) = self.rp_clauses.pop()?;

        match last_rp_clause {
            RpClause::Unit(literal) => {
                self.backtrack_one_level();

                let _ = self.rp_unit_clauses.remove(&literal);
            }

            RpClause::ClauseRef(reference) => {
                let _ = self.solver.delete_allocated_clause(reference);
                let _ = self
                    .rp_allocated_clauses
                    .remove(&reference)
                    .expect("the reference should be for an rp clause");
            }
        }

        // The now removed clause may have caused root-level unsatisfiability. Now that it is
        // removed, we should be able to use the solver again.
        self.solver.declare_ready();

        Some(input_clause)
    }

    /// Perform unit propagation under assumptions.
    ///
    /// In case the engine discovers a conflict, the engine will be in a conflicting state. At this
    /// point, no new clauses can be added before a call to [`RpEngine::remove_last_rp_clause`].
    pub(crate) fn propagate_under_assumptions(
        &mut self,
        assumptions: impl IntoIterator<Item = Literal>,
    ) -> Result<(), Vec<ConflictReason>> {
        assert!(!self.solver.is_conflicting());

        self.solver.declare_new_decision_level();

        for assumption in assumptions.into_iter() {
            let enqueue_result = self.enqueue_and_propagate(assumption);

            if let Err(reasons) = enqueue_result {
                self.backtrack_one_level();
                return Err(reasons);
            }
        }

        self.backtrack_one_level();

        Ok(())
    }

    fn backtrack_one_level(&mut self) {
        self.solver
            .backtrack(self.solver.get_decision_level() - 1, &mut DummyBrancher);
        self.solver.state.declare_solving();
    }

    fn enqueue_and_propagate(
        &mut self,
        literal: Literal,
    ) -> Result<(), ReversePropagationConflict> {
        if !self.solver.enqueue_assumption_literal(literal) {
            // technically this is fine, but it would be surprising to encounter this
            warn!("Unexpected conflict when assigning assumptions.");
            return Err(self.get_conflict_reasons());
        }

        self.solver.propagate_enqueued(&mut Indefinite);

        if self.solver.is_conflicting() {
            Err(self.get_conflict_reasons())
        } else {
            Ok(())
        }
    }

    fn get_conflict_reasons(&mut self) -> Vec<ConflictReason> {
        let mut reasons = Vec::new();

        let mut seen = HashSet::<Literal>::default();

        let mut queue = self.initialise_explain_queue(&mut reasons);

        while let Some(to_explain) = queue.pop() {
            if !seen.insert(to_explain) {
                continue;
            }

            assert!(self
                .solver
                .assignments_propositional
                .is_literal_assigned_true(to_explain));

            if let Some(handle) = self.rp_unit_clauses.get(&to_explain) {
                reasons.push(ConflictReason::Clause(*handle));
            }

            let reference = self
                .solver
                .assignments_propositional
                .get_literal_reason_constraint(to_explain);

            if reference.is_null() {
                continue;
            } else if reference.is_clause() {
                let clause = reference.as_clause_reference();
                if let Some(handle) = self.rp_allocated_clauses.get(&clause) {
                    reasons.push(ConflictReason::Clause(*handle));
                }
                let clause = &self.solver.clause_allocator[clause];
                queue.extend(clause.get_literal_slice().iter().skip(1).map(|&lit| !lit));
            } else if reference.is_cp_reason() {
                let reason = reference.get_reason_ref();
                let propagator = self.solver.reason_store.get_propagator(reason);
                let tag = self.solver.propagator_tags[propagator];
                let name = self.solver.cp_propagators[propagator].name();
                let label = name_to_inference_label(name);

                let conjunction = self
                    .solver
                    .reason_store
                    .get_or_compute(
                        reason,
                        &PropagationContext::new(
                            &self.solver.assignments_integer,
                            &self.solver.assignments_propositional,
                            true,
                            true,
                        ),
                    )
                    .unwrap();

                let premises = conjunction
                    .iter()
                    .filter_map(|predicate| match predicate {
                        Predicate::IntegerPredicate(p) => {
                            Some(self.solver.variable_literal_mappings.get_literal(
                                *p,
                                &self.solver.assignments_propositional,
                                &self.solver.assignments_integer,
                            ))
                        }
                        Predicate::Literal(_) => {
                            panic!("Literals are not propagated in this course")
                        }
                        Predicate::False => panic!("False predicate in conflict conjunction"),
                        Predicate::True => None,
                    })
                    .collect::<Vec<_>>();

                reasons.push(ConflictReason::Propagator {
                    premises: premises.clone(),
                    propagated: Some(to_explain),
                    tag,
                    label,
                });

                queue.extend(premises);
            } else {
                unreachable!("the reference is either a propagation or a clause")
            }
        }

        reasons
    }

    fn initialise_explain_queue(&mut self, reasons: &mut Vec<ConflictReason>) -> Vec<Literal> {
        if let Some(violated_assumption) = self.solver.state.get_violated_assumption() {
            // In this case, one of the assumptions is directly contradicted by previous fixpoint
            // propagation. In that case, we explain why the opposite of the violated assumption is
            // true, to capture everything involved in the conflict.
            return vec![!violated_assumption];
        }

        let conflict_info = self.solver.state.get_conflict_info();

        match conflict_info {
            StoredConflictInfo::VirtualBinaryClause { .. } => unreachable!(),
            StoredConflictInfo::Propagation { reference, literal } => {
                if reference.is_clause() {
                    let clause = reference.as_clause_reference();
                    if let Some(handle) = self.rp_allocated_clauses.get(&clause) {
                        reasons.push(ConflictReason::Clause(*handle));
                    }
                    let clause = &self.solver.clause_allocator[clause];
                    clause.get_literal_slice().iter().map(|&lit| !lit).collect()
                } else if reference.is_cp_reason() {
                    let reason = reference.get_reason_ref();
                    let propagator = self.solver.reason_store.get_propagator(reason);
                    let name = self.solver.cp_propagators[propagator].name();
                    let label = name_to_inference_label(name);

                    let tag = self.solver.propagator_tags[propagator];

                    let conjunction = self
                        .solver
                        .reason_store
                        .get_or_compute(
                            reason,
                            &PropagationContext::new(
                                &self.solver.assignments_integer,
                                &self.solver.assignments_propositional,
                                true,
                                true,
                            ),
                        )
                        .unwrap();

                    let premises = conjunction
                        .iter()
                        .filter_map(|predicate| match predicate {
                            Predicate::IntegerPredicate(p) => {
                                Some(self.solver.variable_literal_mappings.get_literal(
                                    *p,
                                    &self.solver.assignments_propositional,
                                    &self.solver.assignments_integer,
                                ))
                            }
                            Predicate::Literal(_) => {
                                panic!("Literals are not propagated in this course")
                            }
                            Predicate::False => panic!("False predicate in conflict conjunction"),
                            Predicate::True => None,
                        })
                        .collect::<Vec<_>>();

                    reasons.push(ConflictReason::Propagator {
                        premises: premises.clone(),
                        propagated: Some(*literal),
                        tag,
                        label,
                    });

                    premises
                } else {
                    unreachable!("the reference is either a propagation or a clause")
                }
            }

            StoredConflictInfo::Explanation {
                conjunction,
                propagator,
            } => {
                let name = self.solver.cp_propagators[propagator].name();
                let label = name_to_inference_label(name);

                let premises = conjunction
                    .iter()
                    .filter_map(|predicate| match predicate {
                        Predicate::IntegerPredicate(p) => {
                            Some(self.solver.variable_literal_mappings.get_literal(
                                *p,
                                &self.solver.assignments_propositional,
                                &self.solver.assignments_integer,
                            ))
                        }
                        Predicate::Literal(_) => {
                            panic!("Literals are not propagated in this course")
                        }
                        Predicate::False => panic!("False predicate in conflict conjunction"),
                        Predicate::True => None,
                    })
                    .collect::<Vec<_>>();

                reasons.push(ConflictReason::Propagator {
                    premises: premises.clone(),
                    propagated: None,
                    tag: self.solver.propagator_tags[propagator],
                    label,
                });

                premises
            }
        }
    }
}

#[derive(Debug)]
enum RpClause {
    Unit(Literal),
    ClauseRef(ClauseReference),
}

/// We need this to call [`ConstraintSatisfactionSolver::backtrack`], however, it does
/// not need to do anything because [`Brancher::next_decision`] will never be called.
struct DummyBrancher;

impl Brancher for DummyBrancher {
    fn next_decision(&mut self, _: &mut SelectionContext) -> Option<Predicate> {
        None
    }
}

fn name_to_inference_label(name: &str) -> &'static str {
    match name {
        "LinearLeq" => inference_labels::LINEAR,
        "Element" => inference_labels::ELEMENT,
        "Maximum" => inference_labels::MAXIMUM,
        "AllDifferent" => inference_labels::ALL_DIFFERENT,
        "ForwardCheckingCircuit" => inference_labels::PREVENT_AND_CHECK,
        "TimeTable" => inference_labels::TIME_TABLE,

        unknown => panic!("propagator {unknown} not supported in the proof processor"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constraints;
    use crate::engine::variables::DomainId;
    use crate::engine::variables::TransformableVariable;
    use crate::predicate;

    #[test]
    fn rp_clauses_are_removed_in_reverse_order_of_being_added() {
        let mut solver = Solver::default();
        let xs: Vec<Literal> = solver.new_literals().take(3).collect();

        let c1 = xs.clone();
        let c2 = vec![!xs[0], xs[1], !xs[2]];
        let c3 = vec![!xs[0], xs[2]];

        let mut checker = RpEngine::new(solver);
        let _ = checker.add_rp_clause(c1.clone()).unwrap();
        let _ = checker.add_rp_clause(c2.clone()).unwrap();
        let _ = checker.add_rp_clause(c3.clone()).unwrap();

        assert_eq!(Some(c3), checker.remove_last_rp_clause());
        assert_eq!(Some(c2), checker.remove_last_rp_clause());
        assert_eq!(Some(c1), checker.remove_last_rp_clause());
    }

    #[test]
    fn propositional_unsat_proof() {
        let mut solver = Solver::default();
        let xs: Vec<Literal> = solver.new_literals().take(2).collect();

        let _ = solver.add_clause(xs.clone());
        let _ = solver.add_clause([xs[0], !xs[1]]);
        let _ = solver.add_clause([!xs[0], xs[1]]);
        let _ = solver.add_clause([!xs[0], !xs[1]]);

        let mut checker = RpEngine::new(solver);
        let result = checker
            .add_rp_clause([xs[0]])
            .expect_err("no unit-propagation conflict");
        drop(result);

        let clause = checker.remove_last_rp_clause();
        assert_eq!(Some(vec![xs[0]]), clause);

        checker
            .propagate_under_assumptions([])
            .expect("without assumptions no conflict is detected with unit-propagation");

        let _ = checker
            .propagate_under_assumptions([!xs[0]])
            .expect_err("the assumptions should lead to unit propagation-detecting a conflict");
    }

    #[test]
    fn propositional_unsat_get_propagations() {
        let mut solver = Solver::default();
        let xs: Vec<Literal> = solver.new_literals().take(2).collect();

        let _ = solver.add_clause(xs.clone());
        let _ = solver.add_clause([xs[0], !xs[1]]);
        let _ = solver.add_clause([!xs[0], xs[1]]);
        let _ = solver.add_clause([!xs[0], !xs[1]]);

        let mut checker = RpEngine::new(solver);
        let result = checker
            .add_rp_clause([xs[0]])
            .expect_err("no unit-propagation conflict");
        drop(result);
    }

    #[test]
    fn fixing_a_queen_in_3queens_triggers_conflict_under_rp() {
        let (solver, queens) = create_3queens();

        let proof_c1 = [solver.get_literal(predicate![queens[0] == 0])];
        let mut checker = RpEngine::new(solver);

        if checker.propagate_under_assumptions(proof_c1).is_ok() {
            panic!("expected propagation to detect conflict")
        }
    }

    #[test]
    fn with_deletable_clauses_3queens_is_unsat_under_propagation() {
        let (solver, queens) = create_3queens();

        let lit_q0_neq_0 = solver.get_literal(predicate![queens[0] != 0]);
        let lit_q0_neq_1 = solver.get_literal(predicate![queens[0] != 1]);

        let proof_c1 = [lit_q0_neq_0];
        let proof_c2 = [lit_q0_neq_1];

        let mut checker = RpEngine::new(solver);
        let _ = checker.add_rp_clause(proof_c1);

        if checker.add_rp_clause(proof_c2).is_ok() {
            panic!("expected propagation to detect conflict")
        }
    }

    fn create_3queens() -> (Solver, Vec<DomainId>) {
        let mut solver = Solver::default();

        let queens = (0..3)
            .map(|_| solver.new_bounded_integer(0, 2))
            .collect::<Vec<_>>();
        let _ = solver
            .add_constraint(constraints::all_different(queens.clone()))
            .post(NonZero::new(1).unwrap());
        let _ = solver
            .add_constraint(constraints::all_different(
                queens
                    .iter()
                    .enumerate()
                    .map(|(i, var)| var.offset(i as i32))
                    .collect::<Vec<_>>(),
            ))
            .post(NonZero::new(2).unwrap());
        let _ = solver
            .add_constraint(constraints::all_different(
                queens
                    .iter()
                    .enumerate()
                    .map(|(i, var)| var.offset(-(i as i32)))
                    .collect::<Vec<_>>(),
            ))
            .post(NonZero::new(3).unwrap());

        (solver, queens)
    }
}
