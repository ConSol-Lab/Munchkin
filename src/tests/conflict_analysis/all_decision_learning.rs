#![cfg(test)]

use rand::rngs::SmallRng;
use rand::SeedableRng;

use crate::branching::Brancher;
use crate::branching::SelectionContext;
use crate::engine::conflict_analysis::AllDecisionLearning;
use crate::engine::conflict_analysis::ConflictAnalysisContext;
use crate::engine::conflict_analysis::ConflictResolver;
use crate::engine::constraint_satisfaction_solver::CSPSolverState;
use crate::engine::constraint_satisfaction_solver::ClauseMinimisationStrategy;
use crate::engine::constraint_satisfaction_solver::ConflictResolutionStrategy;
use crate::engine::constraint_satisfaction_solver::Counters;
use crate::engine::cp::PropagatorQueue;
use crate::engine::sat::ExplanationClauseManager;
use crate::engine::test_helper::TestSolver;
use crate::options::SolverOptions;
use crate::predicates::Predicate;

struct DummyBrancher;
impl Brancher for DummyBrancher {
    fn next_decision(&mut self, _context: &mut SelectionContext) -> Option<Predicate> {
        todo!()
    }
}

/// Based on Example 4.2.4 from https://www3.cs.stonybrook.edu/~cram/cse505/Fall20/Resources/cdcl.pdf
#[test]
fn test_all_decision() {
    let mut solver = TestSolver::default();

    let x31 = solver.new_literal();
    let x1 = solver.new_literal();
    let x2 = solver.new_literal();
    let x3 = solver.new_literal();
    let x4 = solver.new_literal();
    let x5 = solver.new_literal();
    let x6 = solver.new_literal();
    let x21 = solver.new_literal();

    let _ = solver.add_clause(vec![x1, x31, !x2]);
    let _ = solver.add_clause(vec![x1, !x3]);
    let _ = solver.add_clause(vec![x2, x3, x4]);
    let _ = solver.add_clause(vec![!x4, !x5]);
    let _ = solver.add_clause(vec![x21, !x4, !x6]);
    let _ = solver.add_clause(vec![x5, x6]);

    solver.increase_decision_level();
    solver.set_decision(!x21);

    solver.increase_decision_level();
    solver.set_decision(!x31);

    solver.increase_decision_level();
    solver.set_decision(!x1);

    let mut state = CSPSolverState::default();
    let result = solver.propagate_clausal_propagator();
    if let Err(conflict_info) = result {
        state.declare_conflict(conflict_info.try_into().unwrap());
    } else {
        panic!("Should have been an error");
    }

    let mut resolver = AllDecisionLearning::default();
    let learned_nogood = resolver
        .resolve_conflict(&mut ConflictAnalysisContext {
            clausal_propagator: &mut solver.clausal_propagator,
            variable_literal_mappings: &solver.variable_literal_mappings,
            assignments_integer: &mut solver.assignments_integer,
            assignments_propositional: &mut solver.assignments_propositional,
            internal_parameters: &SolverOptions {
                random_generator: SmallRng::seed_from_u64(42),
                conflict_resolver: ConflictResolutionStrategy::AllDecision,
                minimisation_strategy: ClauseMinimisationStrategy::default(),
            },
            assumptions: &vec![],
            solver_state: &mut state,
            brancher: &mut DummyBrancher,
            clause_allocator: &mut solver.clause_allocator,
            explanation_clause_manager: &mut ExplanationClauseManager::default(),
            reason_store: &mut solver.reason_store,
            counters: &mut Counters::default(),
            propositional_trail_index: &mut 0,
            propagator_queue: &mut PropagatorQueue::new(0),
            watch_list_cp: &mut solver.watch_list,
            sat_trail_synced_position: &mut 0,
            cp_trail_synced_position: &mut 0,
        })
        .expect("Expected learned clause to be returned");

    assert_eq!(learned_nogood.literals, vec![!x1, !x31, !x21]);
    assert_eq!(learned_nogood.backjump_level, 2);
}
