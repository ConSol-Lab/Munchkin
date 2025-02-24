#![cfg(test)]

use crate::engine::conflict_analysis::LearnedNogood;
use crate::engine::cp::reason::ReasonStore;
use crate::engine::cp::AssignmentsInteger;
use crate::engine::cp::VariableLiteralMappings;
use crate::engine::cp::WatchListCP;
use crate::engine::cp::WatchListPropositional;
use crate::engine::minimisation::MinimisationContext;
use crate::engine::minimisation::Minimiser;
use crate::engine::minimisation::SemanticMinimiser;
use crate::engine::sat::AssignmentsPropositional;
use crate::engine::sat::ClausalPropagator;
use crate::engine::sat::ClauseAllocator;
use crate::engine::sat::ExplanationClauseManager;
use crate::predicate;
use crate::predicates::Predicate;
use crate::variables::Literal;

fn create_for_testing(
    num_integer_variables: usize,
    num_propositional_variables: usize,
    domains: Option<Vec<(i32, i32)>>,
) -> (
    AssignmentsInteger,
    AssignmentsPropositional,
    VariableLiteralMappings,
) {
    assert!({
        if let Some(domains) = domains.as_ref() {
            num_integer_variables == domains.len()
        } else {
            true
        }
    });

    let mut mediator = VariableLiteralMappings::default();
    let mut clausal_propagator = ClausalPropagator::default();
    let mut assignments_propositional = AssignmentsPropositional::default();
    let mut assignments_integer = AssignmentsInteger::default();
    let mut clause_allocator = ClauseAllocator::default();
    let mut watch_list_propositional = WatchListPropositional::default();
    let mut watch_list_cp = WatchListCP::default();

    let root_variable = mediator.create_new_propositional_variable(
        &mut watch_list_propositional,
        &mut clausal_propagator,
        &mut assignments_propositional,
    );
    let true_literal = Literal::new(root_variable, true);

    assignments_propositional.true_literal = true_literal;

    assignments_propositional.false_literal = !true_literal;

    assignments_propositional.enqueue_decision_literal(true_literal);

    if let Some(domains) = domains.as_ref() {
        for (_, (lower_bound, upper_bound)) in (0..num_integer_variables).zip(domains) {
            let _ = mediator.create_new_domain(
                *lower_bound,
                *upper_bound,
                &mut assignments_integer,
                &mut watch_list_cp,
                &mut watch_list_propositional,
                &mut clausal_propagator,
                &mut assignments_propositional,
                &mut clause_allocator,
            );
        }
    } else {
        for _ in 0..num_integer_variables {
            let _ = mediator.create_new_domain(
                0,
                10,
                &mut assignments_integer,
                &mut watch_list_cp,
                &mut watch_list_propositional,
                &mut clausal_propagator,
                &mut assignments_propositional,
                &mut clause_allocator,
            );
        }
    }

    for _ in 0..num_propositional_variables {
        // We create an additional variable to ensure that the generator returns the correct
        // variables
        let _ = mediator.create_new_propositional_variable(
            &mut watch_list_propositional,
            &mut clausal_propagator,
            &mut assignments_propositional,
        );
    }

    (assignments_integer, assignments_propositional, mediator)
}

pub(super) fn assert_elements_equal(first: Vec<Literal>, second: Vec<Literal>) {
    assert_eq!(first.len(), second.len(),);
    assert!(first.iter().all(|literal| second.contains(literal)));
    assert!(second.iter().all(|literal| first.contains(literal)));
}

fn predicates_to_nogood(
    clause: Vec<Predicate>,
    variable_literal_mappings: &VariableLiteralMappings,
    assignments_integer: &AssignmentsInteger,
    assignments_propositional: &AssignmentsPropositional,
) -> LearnedNogood {
    LearnedNogood::new(
        clause
            .iter()
            .map(|predicate| {
                variable_literal_mappings.get_literal(
                    (*predicate).try_into().unwrap(),
                    assignments_propositional,
                    assignments_integer,
                )
            })
            .collect::<Vec<_>>(),
        0,
    )
}

#[test]
fn simple_bound1() {
    let mut p = SemanticMinimiser::default();
    let (assignments_integer, assignments_propositional, variable_literal_mappings) =
        create_for_testing(2, 0, Some(vec![(0, 10), (0, 5)]));
    let domain_0 = assignments_integer.get_domains().next().unwrap();
    let domain_1 = assignments_integer.get_domains().nth(1).unwrap();
    let clause: Vec<Predicate> = vec![
        predicate![domain_0 >= 5],
        predicate![domain_0 <= 9],
        predicate![domain_1 >= 0],
        predicate![domain_1 <= 4],
    ];
    let mut learned_nogood = predicates_to_nogood(
        clause,
        &variable_literal_mappings,
        &assignments_integer,
        &assignments_propositional,
    );

    let (mut explanation_manager, mut reason_store, clausal_propagator, mut clause_allocator) = (
        ExplanationClauseManager::default(),
        ReasonStore::default(),
        ClausalPropagator::default(),
        ClauseAllocator::default(),
    );
    let context = MinimisationContext::new(
        &assignments_integer,
        &assignments_propositional,
        &variable_literal_mappings,
        &mut explanation_manager,
        &mut reason_store,
        &clausal_propagator,
        &mut clause_allocator,
    );

    p.minimise(context, &mut learned_nogood);

    assert_eq!(learned_nogood.literals.len(), 3);
    assert_elements_equal(
        learned_nogood.literals,
        predicates_to_nogood(
            vec![
                predicate![domain_0 >= 5],
                predicate![domain_0 <= 9],
                predicate![domain_1 <= 4],
            ],
            &variable_literal_mappings,
            &assignments_integer,
            &assignments_propositional,
        )
        .literals,
    );
}

#[test]
fn simple_bound2() {
    let mut p = SemanticMinimiser::default();
    let (assignments_integer, assignments_propositional, variable_literal_mappings) =
        create_for_testing(2, 0, Some(vec![(0, 10), (0, 5)]));
    let domain_0 = assignments_integer.get_domains().next().unwrap();
    let domain_1 = assignments_integer.get_domains().nth(1).unwrap();

    let clause = vec![
        predicate![domain_0 >= 5],
        predicate![domain_0 <= 9],
        predicate![domain_1 >= 0],
        predicate![domain_1 <= 4],
        predicate![domain_0 != 7],
    ];
    let mut learned_nogood = predicates_to_nogood(
        clause,
        &variable_literal_mappings,
        &assignments_integer,
        &assignments_propositional,
    );

    let (mut explanation_manager, mut reason_store, clausal_propagator, mut clause_allocator) = (
        ExplanationClauseManager::default(),
        ReasonStore::default(),
        ClausalPropagator::default(),
        ClauseAllocator::default(),
    );
    let context = MinimisationContext::new(
        &assignments_integer,
        &assignments_propositional,
        &variable_literal_mappings,
        &mut explanation_manager,
        &mut reason_store,
        &clausal_propagator,
        &mut clause_allocator,
    );

    p.minimise(context, &mut learned_nogood);

    assert_eq!(learned_nogood.literals.len(), 4);
    assert_elements_equal(
        learned_nogood.literals,
        predicates_to_nogood(
            vec![
                predicate![domain_0 >= 5],
                predicate![domain_0 <= 9],
                predicate![domain_1 <= 4],
                predicate![domain_0 != 7],
            ],
            &variable_literal_mappings,
            &assignments_integer,
            &assignments_propositional,
        )
        .literals,
    );
}

#[test]
fn simple_bound3() {
    let mut p = SemanticMinimiser::default();
    let (assignments_integer, assignments_propositional, variable_literal_mappings) =
        create_for_testing(2, 0, Some(vec![(0, 10), (0, 5)]));
    let domain_0 = assignments_integer.get_domains().next().unwrap();
    let domain_1 = assignments_integer.get_domains().nth(1).unwrap();

    let clause = vec![
        predicate![domain_0 >= 5],
        predicate![domain_0 <= 9],
        predicate![domain_1 >= 0],
        predicate![domain_1 <= 4],
        predicate![domain_0 != 7],
        predicate![domain_0 != 7],
        predicate![domain_0 != 8],
        predicate![domain_0 != 6],
    ];
    let mut learned_nogood = predicates_to_nogood(
        clause,
        &variable_literal_mappings,
        &assignments_integer,
        &assignments_propositional,
    );

    let (mut explanation_manager, mut reason_store, clausal_propagator, mut clause_allocator) = (
        ExplanationClauseManager::default(),
        ReasonStore::default(),
        ClausalPropagator::default(),
        ClauseAllocator::default(),
    );
    let context = MinimisationContext::new(
        &assignments_integer,
        &assignments_propositional,
        &variable_literal_mappings,
        &mut explanation_manager,
        &mut reason_store,
        &clausal_propagator,
        &mut clause_allocator,
    );

    p.minimise(context, &mut learned_nogood);

    assert_eq!(learned_nogood.literals.len(), 6);
    assert_elements_equal(
        learned_nogood.literals,
        predicates_to_nogood(
            vec![
                predicate![domain_0 >= 5],
                predicate![domain_0 <= 9],
                predicate![domain_1 <= 4],
                predicate![domain_0 != 7],
                predicate![domain_0 != 6],
                predicate![domain_0 != 8],
            ],
            &variable_literal_mappings,
            &assignments_integer,
            &assignments_propositional,
        )
        .literals,
    )
}

#[test]
fn simple_assign() {
    let mut p = SemanticMinimiser::default();
    let (assignments_integer, assignments_propositional, variable_literal_mappings) =
        create_for_testing(2, 0, Some(vec![(0, 10), (0, 5)]));
    let domain_0 = assignments_integer.get_domains().next().unwrap();
    let domain_1 = assignments_integer.get_domains().nth(1).unwrap();

    let clause = vec![
        predicate![domain_0 >= 5],
        predicate![domain_0 <= 9],
        predicate![domain_1 >= 0],
        predicate![domain_1 <= 4],
        predicate![domain_0 != 7],
        predicate![domain_0 != 7],
        predicate![domain_0 != 6],
        predicate![domain_0 == 5],
        predicate![domain_0 != 7],
    ];
    let mut learned_nogood = predicates_to_nogood(
        clause,
        &variable_literal_mappings,
        &assignments_integer,
        &assignments_propositional,
    );
    let (mut explanation_manager, mut reason_store, clausal_propagator, mut clause_allocator) = (
        ExplanationClauseManager::default(),
        ReasonStore::default(),
        ClausalPropagator::default(),
        ClauseAllocator::default(),
    );
    let context = MinimisationContext::new(
        &assignments_integer,
        &assignments_propositional,
        &variable_literal_mappings,
        &mut explanation_manager,
        &mut reason_store,
        &clausal_propagator,
        &mut clause_allocator,
    );

    p.minimise(context, &mut learned_nogood);

    assert_eq!(learned_nogood.literals.len(), 2);
    assert_elements_equal(
        learned_nogood.literals,
        predicates_to_nogood(
            vec![predicate![domain_0 == 5], predicate![domain_1 <= 4]],
            &variable_literal_mappings,
            &assignments_integer,
            &assignments_propositional,
        )
        .literals,
    )
}

#[test]
fn simple_lb_override1() {
    let mut p = SemanticMinimiser::default();
    let (assignments_integer, assignments_propositional, variable_literal_mappings) =
        create_for_testing(1, 0, None);
    let domain_id = assignments_integer.get_domains().next().unwrap();
    let clause = vec![
        predicate![domain_id >= 2],
        predicate![domain_id >= 1],
        predicate![domain_id >= 5],
    ];
    let mut learned_nogood = predicates_to_nogood(
        clause,
        &variable_literal_mappings,
        &assignments_integer,
        &assignments_propositional,
    );
    let (mut explanation_manager, mut reason_store, clausal_propagator, mut clause_allocator) = (
        ExplanationClauseManager::default(),
        ReasonStore::default(),
        ClausalPropagator::default(),
        ClauseAllocator::default(),
    );
    let context = MinimisationContext::new(
        &assignments_integer,
        &assignments_propositional,
        &variable_literal_mappings,
        &mut explanation_manager,
        &mut reason_store,
        &clausal_propagator,
        &mut clause_allocator,
    );

    p.minimise(context, &mut learned_nogood);

    assert_eq!(learned_nogood.literals.len(), 1);
    assert_eq!(
        learned_nogood.literals[0],
        variable_literal_mappings.get_literal(
            predicate!(domain_id >= 5).try_into().unwrap(),
            &assignments_propositional,
            &assignments_integer
        )
    );
}

#[test]
fn hole_lb_override() {
    let mut p = SemanticMinimiser::default();
    let (assignments_integer, assignments_propositional, variable_literal_mappings) =
        create_for_testing(1, 0, None);
    let domain_id = assignments_integer.get_domains().next().unwrap();
    let clause = vec![
        predicate![domain_id != 2],
        predicate![domain_id != 3],
        predicate![domain_id >= 5],
        predicate![domain_id >= 1],
    ];
    let mut learned_nogood = predicates_to_nogood(
        clause,
        &variable_literal_mappings,
        &assignments_integer,
        &assignments_propositional,
    );

    let (mut explanation_manager, mut reason_store, clausal_propagator, mut clause_allocator) = (
        ExplanationClauseManager::default(),
        ReasonStore::default(),
        ClausalPropagator::default(),
        ClauseAllocator::default(),
    );
    let context = MinimisationContext::new(
        &assignments_integer,
        &assignments_propositional,
        &variable_literal_mappings,
        &mut explanation_manager,
        &mut reason_store,
        &clausal_propagator,
        &mut clause_allocator,
    );

    p.minimise(context, &mut learned_nogood);

    assert_eq!(learned_nogood.literals.len(), 1);
    assert_elements_equal(
        learned_nogood.literals,
        predicates_to_nogood(
            vec![predicate!(domain_id >= 5)],
            &variable_literal_mappings,
            &assignments_integer,
            &assignments_propositional,
        )
        .literals,
    )
}

#[test]
fn hole_push_lb() {
    let mut p = SemanticMinimiser::default();
    let (assignments_integer, assignments_propositional, variable_literal_mappings) =
        create_for_testing(1, 0, None);
    let domain_id = assignments_integer.get_domains().next().unwrap();
    let clause = vec![
        predicate![domain_id != 2],
        predicate![domain_id != 3],
        predicate![domain_id >= 1],
        predicate![domain_id != 1],
    ];
    let mut learned_nogood = predicates_to_nogood(
        clause,
        &variable_literal_mappings,
        &assignments_integer,
        &assignments_propositional,
    );

    let (mut explanation_manager, mut reason_store, clausal_propagator, mut clause_allocator) = (
        ExplanationClauseManager::default(),
        ReasonStore::default(),
        ClausalPropagator::default(),
        ClauseAllocator::default(),
    );
    let context = MinimisationContext::new(
        &assignments_integer,
        &assignments_propositional,
        &variable_literal_mappings,
        &mut explanation_manager,
        &mut reason_store,
        &clausal_propagator,
        &mut clause_allocator,
    );

    p.minimise(context, &mut learned_nogood);

    assert_eq!(learned_nogood.literals.len(), 1);
    assert_elements_equal(
        learned_nogood.literals,
        predicates_to_nogood(
            vec![predicate![domain_id >= 4]],
            &variable_literal_mappings,
            &assignments_integer,
            &assignments_propositional,
        )
        .literals,
    )
}
