use log::warn;

use super::ClauseAllocator;
use crate::basic_types::ClauseReference;
use crate::basic_types::ConflictInfo;
use crate::basic_types::ConstraintOperationError;
use crate::basic_types::HashMap;
use crate::basic_types::KeyedVec;
use crate::engine::sat::AssignmentsPropositional;
use crate::engine::variables::Literal;
use crate::engine::Preprocessor;
use crate::munchkin_assert_moderate;
use crate::munchkin_assert_simple;

#[derive(Default, Debug)]
pub(crate) struct ClausalPropagator {
    pub(crate) watch_lists: KeyedVec<Literal, Vec<ClauseWatcher>>,
    pub(crate) next_position_on_trail_to_propagate: usize,
    pub(crate) permanent_clauses: Vec<ClauseReference>,
    is_in_infeasible_state: bool,
}

impl ClausalPropagator {
    pub(crate) fn grow(&mut self) {
        // increase the watch list, once for each polarity
        self.watch_lists.push(vec![]);
        self.watch_lists.push(vec![]);
    }

    pub(crate) fn get_literal_propagation_clause_reference(
        &self,
        propagated_literal: Literal,
        assignments: &AssignmentsPropositional,
    ) -> ClauseReference {
        munchkin_assert_moderate!(assignments
            .get_literal_reason_constraint(propagated_literal)
            .is_clause());

        let clause_reference: ClauseReference = assignments
            .get_literal_reason_constraint(propagated_literal)
            .into();
        munchkin_assert_moderate!(clause_reference.is_allocated_clause());

        clause_reference
    }

    pub(crate) fn add_permanent_clause(
        &mut self,
        literals: Vec<Literal>,
        assignments: &mut AssignmentsPropositional,
        clause_allocator: &mut ClauseAllocator,
    ) -> Result<(), ConstraintOperationError> {
        munchkin_assert_simple!(assignments.is_at_the_root_level());

        if self.is_in_infeasible_state {
            return Err(ConstraintOperationError::InfeasibleState);
        }

        if literals.is_empty() {
            warn!("Adding empty clause, unusual!");
        }

        let literals = Preprocessor::preprocess_clause(literals, assignments);

        // infeasible at the root? Note that we do not add the original clause to the database in
        // this case
        if literals.is_empty() {
            self.is_in_infeasible_state = true;
            return Err(ConstraintOperationError::InfeasibleClause);
        }

        // is unit clause? Unit clauses are added as root assignments, rather than as actual clauses
        // 	in case the clause is satisfied at the root, the PreprocessClause method will return a
        // unit clause with a literal that is satisfied at the root

        // add clause unit
        if literals.len() == 1 {
            if assignments.is_literal_assigned_false(literals[0]) {
                self.is_in_infeasible_state = true;
                return Err(ConstraintOperationError::InfeasibleClause);
            } else if assignments.is_literal_unassigned(literals[0]) {
                assignments.enqueue_decision_literal(literals[0]);
                let outcome = self.propagate(assignments, clause_allocator);
                if outcome.is_err() {
                    self.is_in_infeasible_state = true;
                    return Err(ConstraintOperationError::InfeasibleClause);
                }
            }
        } else {
            // standard case - the clause has at least two unassigned literals
            let _ = self.add_clause_unchecked(literals, false, clause_allocator);
        }

        Ok(())
    }

    #[allow(unused, reason = "can be used in assignment")]
    pub(crate) fn add_asserting_learned_clause(
        &mut self,
        literals: Vec<Literal>,
        assignments: &mut AssignmentsPropositional,
        clause_allocator: &mut ClauseAllocator,
    ) -> Option<ClauseReference> {
        let asserting_literal = literals[0];

        let clause_reference = self
            .add_clause_unchecked(literals, true, clause_allocator)
            .expect("Add clause failed for some reason");

        let _ = assignments.enqueue_propagated_literal(asserting_literal, clause_reference.into());

        Some(clause_reference)
    }

    pub(crate) fn add_clause_unchecked(
        &mut self,
        literals: Vec<Literal>,
        is_learned: bool,
        clause_allocator: &mut ClauseAllocator,
    ) -> Option<ClauseReference> {
        munchkin_assert_moderate!(literals.len() >= 2);
        munchkin_assert_simple!(!self.is_in_infeasible_state);

        let clause_reference = clause_allocator.create_clause(literals, is_learned);
        let clause = clause_allocator.get_clause(clause_reference);

        self.permanent_clauses.push(clause_reference);
        self.start_watching_clause_unchecked(clause.get_literal_slice(), clause_reference);

        Some(clause_reference)
    }

    pub(crate) fn add_permanent_implication_unchecked(
        &mut self,
        lhs: Literal,
        rhs: Literal,
        clause_allocator: &mut ClauseAllocator,
    ) {
        let _ = self.add_clause_unchecked(vec![!lhs, rhs], false, clause_allocator);
    }

    pub(crate) fn add_permanent_ternary_clause_unchecked(
        &mut self,
        a: Literal,
        b: Literal,
        c: Literal,
        clause_allocator: &mut ClauseAllocator,
    ) {
        let _ = self.add_clause_unchecked(vec![a, b, c], false, clause_allocator);
    }

    pub(crate) fn propagate(
        &mut self,
        assignments: &mut AssignmentsPropositional,
        clause_manager: &mut ClauseAllocator,
    ) -> Result<(), ConflictInfo> {
        munchkin_assert_simple!(!self.is_in_infeasible_state);
        // this function is implemented as one long function
        //  dividing this function into several smaller functions would normally make sense for
        // readability  however this is a performance hotspot, so it is hard to divide the
        // code into smaller bits without degrading the performance  so the decision was to
        // not divide the function into smaller parts and simply have one long function
        while self.next_position_on_trail_to_propagate < assignments.num_trail_entries() {
            let true_literal =
                assignments.get_trail_entry(self.next_position_on_trail_to_propagate);
            munchkin_assert_simple!(assignments.is_literal_assigned_true(true_literal));

            // effectively remove all watches from this true_literal
            // then go through the previous watches one by one and insert them as indicated (some
            // might be placed back in the watch list of this true_literal)
            // if a conflict takes place, put back the remaining clauses into the watch list of this
            // true_literal and report the conflict empty watch lists are immediately
            // skipped
            if self.watch_lists[!true_literal].is_empty() {
                self.next_position_on_trail_to_propagate += 1;
                continue;
            }

            // effectively, we are resizing the watch list to size zero for this literal
            //  and in the loop we will add some of the old watches back
            let mut end_index: usize = 0;
            let mut current_index: usize = 0;
            while current_index < self.watch_lists[!true_literal].len() {
                // inspect if the cached literal is already set to true
                // if so, no need to go further in the memory to check the clause
                // often this literal will be true in practice so it is a good heuristic to check
                let cached_literal = self.watch_lists[!true_literal][current_index].cached_literal;
                if assignments.is_literal_assigned_true(cached_literal) {
                    // keep the watcher, the clause is satisfied, no propagation can take place
                    self.watch_lists[!true_literal][end_index] =
                        self.watch_lists[!true_literal][current_index];
                    current_index += 1;
                    end_index += 1;
                    continue;
                }

                let watched_clause_reference =
                    self.watch_lists[!true_literal][current_index].clause_reference;

                let watched_clause = clause_manager.get_mutable_clause(watched_clause_reference);

                // standard clause propagation starts here

                // place the considered literal at position 1 for simplicity
                if watched_clause[0] == !true_literal {
                    watched_clause[0] = watched_clause[1];
                    watched_clause[1] = !true_literal;
                }

                // check the other watched literal to see if the clause is already satisfied
                //  check if this would help in the condition: next_watch_pointer->cached_literal !=
                // watched_clause[0] &&
                if assignments.is_literal_assigned_true(watched_clause[0]) {
                    // take the true literal as the new cached literal -> todo need to check if this
                    // makes sense
                    self.watch_lists[!true_literal][current_index].cached_literal =
                        watched_clause[0];
                    // keep the watcher, the clause is satisfied, no propagation can take place
                    self.watch_lists[!true_literal][end_index] =
                        self.watch_lists[!true_literal][current_index];
                    current_index += 1;
                    end_index += 1;
                    continue;
                }

                // look for another nonfalsified literal to replace one of the watched literals
                let mut found_new_watch = false;
                // start from index 2 since we are skipping watched literals
                for i in 2..watched_clause.len() {
                    // find a literal that is either true or unassigned, i.e., not assigned false
                    if !assignments.is_literal_assigned_false(watched_clause[i]) {
                        // would it make sense to set the cached literal here if this new literal
                        // will be set to true? replace the watched literal,
                        // add the clause to the watch list of the new watcher literal
                        watched_clause[1] = watched_clause[i];
                        watched_clause[i] = !true_literal;

                        self.watch_lists[watched_clause[1]].push(ClauseWatcher {
                            cached_literal: watched_clause[0],
                            clause_reference: watched_clause_reference,
                        });

                        found_new_watch = true;
                        break; // no propagation is taking place, go to the next clause.
                    }
                }

                if found_new_watch {
                    // note this clause is effectively removed from the watch list of true_literal,
                    // since we are only incrementing the current index, and not copying anything to
                    // the end_index location
                    current_index += 1;
                    continue;
                }

                // keep the current watch for this literal
                self.watch_lists[!true_literal][end_index] =
                    self.watch_lists[!true_literal][current_index];
                end_index += 1;
                current_index += 1;

                // at this point, nonwatched literals and literal[1] are assigned false. There are
                // two scenarios: 	watched_clause[0] is unassigned -> propagate the
                // literal to true 	watched_clause[0] is assigned false -> conflict

                // can propagate?
                let conflict_info = assignments
                    .enqueue_propagated_literal(watched_clause[0], watched_clause_reference.into());
                if let Some(conflict_info) = conflict_info {
                    // conflict detected, stop any further propagation and report the conflict
                    //  munchkin_assert_advanced(state_.assignments_.
                    // IsAssignedFalse(watched_clause[0]), "Sanity check.");
                    // readd the remaining watchers to the watch list
                    while current_index < self.watch_lists[!true_literal].len() {
                        self.watch_lists[!true_literal][end_index] =
                            self.watch_lists[!true_literal][current_index];
                        current_index += 1;
                        end_index += 1;
                    }
                    self.watch_lists[!true_literal].truncate(end_index);
                    return Err(conflict_info);
                }
            }
            self.watch_lists[!true_literal].truncate(end_index);
            self.next_position_on_trail_to_propagate += 1;
        }
        Ok(())
    }

    pub(crate) fn synchronise(&mut self, trail_size: usize) {
        munchkin_assert_simple!(self.next_position_on_trail_to_propagate >= trail_size);
        self.next_position_on_trail_to_propagate = trail_size;
    }

    pub(crate) fn is_propagation_complete(&self, trail_size: usize) -> bool {
        self.next_position_on_trail_to_propagate == trail_size
    }

    pub(crate) fn remove_clause_from_consideration(
        &mut self,
        clause: &[Literal],
        clause_reference: ClauseReference,
    ) {
        // for now a simple implementation, in the future it could be worthwhile considering lazy
        // data structure or batch removals
        let remove_clause_from_watchers =
            |watchers: &mut Vec<ClauseWatcher>, clause_reference: ClauseReference| {
                let index = watchers
                    .iter()
                    .position(|x| x.clause_reference == clause_reference)
                    .unwrap();
                let _ = watchers.swap_remove(index);
            };

        let watched_literal1 = clause[0];
        let watched_literal2 = clause[1];

        remove_clause_from_watchers(&mut self.watch_lists[watched_literal1], clause_reference);
        remove_clause_from_watchers(&mut self.watch_lists[watched_literal2], clause_reference);
    }

    pub(crate) fn debug_check_state(
        &self,
        assignments: &AssignmentsPropositional,
        clause_allocator: &ClauseAllocator,
    ) -> bool {
        assert!(
            self.watch_lists.len() as u32 == 2 * assignments.num_propositional_variables(),
            "Watch list length is not as expected given the number of propositional variables."
        );

        assert!(self.is_propagation_complete(assignments.num_trail_entries()), "Only makes sense to check the propagator state after there is nothing left to propagate.");

        // check that each clause that appears in the watch list appears exactly twice
        //  note that not every clause in the clause manager necessarily appears in the watch list

        //  first compute the histogram for each clause present
        let mut clause_ids: HashMap<ClauseReference, usize> = HashMap::default();

        // counting the number of binary clause watchers is a proxy
        //  in case the number is uneven we have a problem
        assert!(
            self.watch_lists
                .iter()
                .flatten()
                .filter(|x| x.clause_reference.is_virtual_binary_clause())
                .count()
                % 2
                == 0,
        );

        assert!(self
            .watch_lists
            .iter()
            .flatten()
            .all(|x| { x.clause_reference.is_allocated_clause() }));

        self.watch_lists.iter().flatten().for_each(|x| {
            *clause_ids.entry(x.clause_reference).or_insert(0) += 1;
        });
        assert!(
            clause_ids.iter().all(|x| *x.1 == 2),
            "There is a clause in the watch list that does not appear exactly twice."
        );

        for literal_code in 0..self.watch_lists.len() {
            let literal = Literal::u32_to_literal(literal_code as u32);
            assert!(self.watch_lists[literal].iter().all(|x| {
                    let clause = clause_allocator.get_clause(x.clause_reference);
                    clause[0] == literal || clause[1] == literal
            }), "The watches are not correct, i.e., there is a clause in the watch list of a literal that is not a watcher of the clause");
        }

        assert!(
            self.watch_lists.iter().flatten().all(|x| {
                let clause = clause_allocator.get_clause(x.clause_reference);
                clause
                    .get_literal_slice()
                    .iter()
                    .any(|lit| *lit == x.cached_literal)
            }),
            "There is a watcher with a cached literal that is not present in the clause."
        );

        // check for each literal that has been propagated by the clausal propagator
        //  whether the propagation was justified, i.e.,
        //      the clause is in the watch list
        //      the clause associated with the propagation has the literal at position 0
        //      the other literals in the clause are all set to false
        //      the propagation level of the propagated literal is equal to the max level of the
        // other literals
        for literal_code in 0..self.watch_lists.len() {
            let literal = Literal::u32_to_literal(literal_code as u32);
            // skip root assignments since the info is not correct tracked for root assignments
            if assignments.is_literal_root_assignment(literal) {
                continue;
            }

            // we only consider literals that have been assigned true through propagation
            //  literals that take value false can be ignored since their negation will be checked
            if assignments.is_literal_propagated(literal)
                && assignments.is_literal_assigned_true(literal)
            {
                let constraint_reference = assignments.get_literal_reason_constraint(literal);

                if constraint_reference.is_clause() {
                    let clause_reference = constraint_reference.into();
                    assert!(
                        clause_ids.contains_key(&clause_reference),
                        "The clause responsible for propagation is not in the watch list."
                    );

                    let clause = clause_allocator.get_clause(clause_reference);
                    assert!(clause[0] == literal, "Literal has been propagated by clause, but the literal is not at position 0 as expected.");
                    assert!(
                        clause.get_literal_slice()[1..]
                            .iter()
                            .all(|x| assignments.is_literal_assigned_false(*x)),
                        "A clause is recorded as the reason for propagation, but the other literals are not all false."
                    );
                    // ensure propagation was done at the correct decision level
                    let lit_max_decision_level = *clause.get_literal_slice()[1..]
                        .iter()
                        .max_by_key(|x| assignments.get_literal_assignment_level(**x))
                        .unwrap();
                    let max_decision_level =
                        assignments.get_literal_assignment_level(lit_max_decision_level);
                    assert!(
                        max_decision_level == assignments.get_literal_assignment_level(literal),
                        "Literal propagation level does not match the other literals."
                    );
                }
            }
        }

        // check if the propagator missed a falsified clause or a propagation
        clause_ids.iter().for_each(|x| {
            let clause = clause_allocator.get_clause(*x.0);
            assert!(
                !clause
                    .get_literal_slice()
                    .iter()
                    .all(|x| assignments.is_literal_assigned_false(*x)),
                "Debugging revealed that the clausal propagator missed a falsifying clause."
            );

            let num_falsified_literals = clause
                .get_literal_slice()
                .iter()
                .filter(|x| assignments.is_literal_assigned_false(**x))
                .count();

            if num_falsified_literals + 1 == clause.len() as usize {
                let true_literal = clause
                    .get_literal_slice()
                    .iter()
                    .find(|x| !assignments.is_literal_assigned_false(**x));
                assert!(
                    assignments.is_literal_assigned_true(*true_literal.unwrap()),
                    "Debugging revealed that the clausal propagator missed a propagation."
                );
            }
        });

        true
    }
}

impl ClausalPropagator {
    fn start_watching_clause_unchecked(
        &mut self,
        clause: &[Literal],
        clause_reference: ClauseReference,
    ) {
        munchkin_assert_simple!(clause.len() >= 2);

        self.watch_lists[clause[0]].push(ClauseWatcher {
            cached_literal: clause[1],
            clause_reference,
        });

        self.watch_lists[clause[1]].push(ClauseWatcher {
            cached_literal: clause[0],
            clause_reference,
        });
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct ClauseWatcher {
    cached_literal: Literal,
    clause_reference: ClauseReference,
}
