#![cfg(test)]

use crate::engine::conflict_analysis::LearnedNogood;
use crate::engine::minimisation::MinimisationContext;
use crate::engine::minimisation::Minimiser;
use crate::engine::minimisation::RecursiveMinimiser;
use crate::engine::sat::AssignmentsPropositional;
use crate::engine::sat::ExplanationClauseManager;
use crate::engine::test_helper::TestSolver;
use crate::tests::minimisation::semantic_minimisation::assert_elements_equal;
use crate::variables::Literal;

#[test]
/// Based on Figure 1 from https://link.springer.com/chapter/10.1007/978-3-642-02777-2_15
fn test_recursive_minimisation() {
    let mut solver = TestSolver::default();
    let mut minimiser = RecursiveMinimiser::default();

    let a = solver.new_literal();
    let b = solver.new_literal();
    let c = solver.new_literal();
    let d = solver.new_literal();
    let z = solver.new_literal();
    let y = solver.new_literal();
    let x = solver.new_literal();
    let w = solver.new_literal();
    let r = solver.new_literal();
    let q = solver.new_literal();
    let p = solver.new_literal();
    let delta = solver.new_literal();
    let s = solver.new_literal();
    let m = solver.new_literal();
    let h = solver.new_literal();
    let gamma = solver.new_literal();
    let t = solver.new_literal();
    let l = solver.new_literal();
    let g = solver.new_literal();
    let beta = solver.new_literal();
    let u = solver.new_literal();
    let k = solver.new_literal();
    let f = solver.new_literal();
    let alpha = solver.new_literal();
    let j = solver.new_literal();
    let e = solver.new_literal();
    let v = solver.new_literal();
    let n = solver.new_literal();
    let i = solver.new_literal();

    let all_literals = [
        a, b, c, d, z, y, x, w, r, q, p, delta, s, m, h, gamma, t, l, g, beta, u, k, f, alpha, j,
        e, v, n, i,
    ];

    let _ = solver.add_clause(vec![!e, !j, !f]);

    let _ = solver.add_clause(vec![e, !k, !g]);
    let _ = solver.add_clause(vec![i, !j, !n]);
    let _ = solver.add_clause(vec![n, !u, !v]);

    let _ = solver.add_clause(vec![v, !alpha]);
    let _ = solver.add_clause(vec![j, !k, !n]);

    let _ = solver.add_clause(vec![alpha, !beta]);
    let _ = solver.add_clause(vec![u, !t]);
    let _ = solver.add_clause(vec![k, !l, !n]);
    let _ = solver.add_clause(vec![f, !i, !h]);

    let _ = solver.add_clause(vec![beta, !gamma]);
    let _ = solver.add_clause(vec![t, !s]);
    let _ = solver.add_clause(vec![l, !t, !s, !m]);
    let _ = solver.add_clause(vec![g, !m, !r, !h, !p]);

    let _ = solver.add_clause(vec![gamma, !delta]);
    let _ = solver.add_clause(vec![s, !r]);
    let _ = solver.add_clause(vec![m, !s, !q, !t]);
    let _ = solver.add_clause(vec![h, !l, !q, !p]);

    let _ = solver.add_clause(vec![delta, !z, !r]);

    let _ = solver.add_clause(vec![r, !y]);
    let _ = solver.add_clause(vec![q, !x]);
    let _ = solver.add_clause(vec![p, !w]);

    let _ = solver.add_clause(vec![z, !a]);
    let _ = solver.add_clause(vec![y, !b]);
    let _ = solver.add_clause(vec![x, !c]);
    let _ = solver.add_clause(vec![w, !d]);

    solver.increase_decision_level();
    solver.set_decision(a);
    let result = solver.propagate_clausal_propagator();
    assert!(result.is_ok());

    solver.increase_decision_level();
    solver.set_decision(b);
    let result = solver.propagate_clausal_propagator();
    assert!(result.is_ok());

    solver.increase_decision_level();
    solver.set_decision(c);
    let result = solver.propagate_clausal_propagator();
    assert!(result.is_ok());

    solver.increase_decision_level();
    solver.set_decision(d);
    let result = solver.propagate_clausal_propagator();
    assert!(result.is_err());

    assert_all_fixed(&all_literals, &solver.assignments_propositional);

    let mut learned_nogood = LearnedNogood::new(vec![p, j, k, i, m, r, l, q], 2);

    let mut explanation_clause_manager = ExplanationClauseManager::default();
    let context = MinimisationContext::new(
        &solver.assignments_integer,
        &solver.assignments_propositional,
        &solver.variable_literal_mappings,
        &mut explanation_clause_manager,
        &mut solver.reason_store,
        &solver.clausal_propagator,
        &mut solver.clause_allocator,
        true,
        true,
    );
    minimiser.minimise(context, &mut learned_nogood);

    assert_elements_equal(learned_nogood.literals, vec![p, j, k, i, r, q])
}

fn assert_all_fixed(
    all_literals: &[Literal],
    assignments_propositional: &AssignmentsPropositional,
) {
    assert!(all_literals
        .iter()
        .all(|literal| assignments_propositional.is_literal_assigned(*literal)))
}
