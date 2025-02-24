//! Houses the solver which attempts to find a solution to a Constraint Satisfaction Problem (CSP)
//! using a Lazy Clause Generation approach.

use std::cmp::min;
use std::fmt::Debug;
use std::fmt::Display;
use std::fmt::Formatter;
use std::time::Instant;

use clap::ValueEnum;
use rand::rngs::SmallRng;
use rand::SeedableRng;

use super::conflict_analysis::AllDecisionLearning;
use super::conflict_analysis::ConflictResolver;
use super::conflict_analysis::LearnedNogood;
use super::conflict_analysis::NoLearning;
use super::conflict_analysis::UniqueImplicationPoint;
use super::cp::propagation::PropagationContext;
use super::minimisation::recompute_invariants;
use super::minimisation::MinimisationContext;
use super::minimisation::RecursiveMinimiser;
use super::minimisation::SemanticMinimiser;
use super::sat::ClauseAllocator;
use super::termination::TerminationCondition;
use super::variables::IntegerVariable;
use super::VariableNames;
use crate::basic_types::statistic_logging::statistic_logger::log_statistic;
use crate::basic_types::CSPSolverExecutionFlag;
use crate::basic_types::ClauseReference;
use crate::basic_types::ConflictInfo;
use crate::basic_types::ConstraintOperationError;
use crate::basic_types::ConstraintReference;
use crate::basic_types::Inconsistency;
use crate::basic_types::PropagationStatusOneStepCP;
use crate::basic_types::SolutionReference;
use crate::basic_types::StoredConflictInfo;
use crate::branching::Brancher;
use crate::branching::SelectionContext;
use crate::engine::conflict_analysis::ConflictAnalysisContext;
use crate::engine::cp::propagation::PropagationContextMut;
use crate::engine::cp::propagation::Propagator;
use crate::engine::cp::propagation::PropagatorId;
use crate::engine::cp::propagation::PropagatorInitialisationContext;
use crate::engine::cp::reason::ReasonStore;
use crate::engine::cp::AssignmentsInteger;
use crate::engine::cp::BooleanDomainEvent;
use crate::engine::cp::EmptyDomain;
use crate::engine::cp::IntDomainEvent;
use crate::engine::cp::PropagatorQueue;
use crate::engine::cp::VariableLiteralMappings;
use crate::engine::cp::WatchListCP;
use crate::engine::cp::WatchListPropositional;
use crate::engine::debug_helper::DebugDyn;
use crate::engine::minimisation::Minimiser;
use crate::engine::predicates::predicate::Predicate;
use crate::engine::sat::calculate_lbd;
use crate::engine::sat::AssignmentsPropositional;
use crate::engine::sat::ClausalPropagator;
use crate::engine::sat::ExplanationClauseManager;
use crate::engine::variables::DomainId;
use crate::engine::variables::Literal;
use crate::engine::variables::PropositionalVariable;
use crate::engine::DebugHelper;
use crate::munchkin_assert_advanced;
use crate::munchkin_assert_extreme;
use crate::munchkin_assert_moderate;
use crate::munchkin_assert_simple;
use crate::termination::Indefinite;
#[cfg(doc)]
use crate::Solver;

/// A solver which attempts to find a solution to a Constraint Satisfaction Problem (CSP) using
/// a Lazy Clause Generation (LCG [\[1\]](https://people.eng.unimelb.edu.au/pstuckey/papers/cp09-lc.pdf))
/// approach.
///
/// The solver maintains two views of the problem, a Constraint Programming (CP) view and a SAT
/// view. It requires that all of the propagators which are added, are able to explain the
/// propagations and conflicts they have made/found. It then uses standard SAT concepts such as
/// 1UIP (see \[2\]) to learn clauses (also called nogoods in the CP field, see \[3\]) to avoid
/// unnecessary exploration of the search space while utilizing the search procedure benefits from
/// constraint programming (e.g. by preventing the exponential blow-up of problem encodings).
///
/// # Practical
/// The [`ConstraintSatisfactionSolver`] makes use of certain options which allow the user to
/// influence the behaviour of the solver; see for example the [`SatisfactionSolverOptions`] and the
/// [`LearningOptions`].
///
/// The solver switches between making decisions using implementations of the [`Brancher`] (which
/// are passed to the [`ConstraintSatisfactionSolver::solve`] method) and propagation (use
/// [`ConstraintSatisfactionSolver::add_propagator`] to add a propagator). If a conflict is found by
/// any of the propagators (including the clausal one) then the solver will analyse the conflict
/// using 1UIP reasoning and backtrack if possible.
///
/// # Bibliography
/// \[1\] T. Feydy and P. J. Stuckey, ‘Lazy clause generation reengineered’, in International
/// Conference on Principles and Practice of Constraint Programming, 2009, pp. 352–366.
///
/// \[2\] J. Marques-Silva, I. Lynce, and S. Malik, ‘Conflict-driven clause learning SAT
/// solvers’, in Handbook of satisfiability, IOS press, 2021
///
/// \[3\] F. Rossi, P. Van Beek, and T. Walsh, ‘Constraint programming’, Foundations of Artificial
/// Intelligence, vol. 3, pp. 181–211, 2008.
pub struct ConstraintSatisfactionSolver {
    /// The solver continuously changes states during the search.
    /// The state helps track additional information and contributes to making the code clearer.
    pub(crate) state: CSPSolverState,
    /// Tracks information related to the assignments of propositional variables.
    pub(crate) assignments_propositional: AssignmentsPropositional,
    /// Responsible for clausal propagation based on the two-watched scheme.
    /// Although technically just another propagator, we treat the clausal propagator in a special
    /// way due to efficiency and conflict analysis.
    clausal_propagator: ClausalPropagator,
    /// The list of propagators. Propagators live here and are queried when events (domain changes)
    /// happen. The list is only traversed during synchronisation for now.
    cp_propagators: Vec<Box<dyn Propagator>>,
    /// Tracks information about all allocated clauses. All clause allocaton goes exclusively
    /// through the clause allocator. There are two notable exceptions:
    /// - Unit clauses are stored directly on the trail.
    /// - Binary clauses may be inlined in the watch lists of the clausal propagator.
    pub(crate) clause_allocator: ClauseAllocator,
    /// Holds the assumptions when the solver is queried to solve under assumptions.
    assumptions: Vec<Literal>,
    /// Resolves and processes the conflict.
    conflict_resolver: Box<dyn ConflictResolver>,
    /// Tracks information related to the assignments of integer variables.
    pub(crate) assignments_integer: AssignmentsInteger,
    /// Contains information on which propagator to notify upon
    /// integer events, e.g., lower or upper bound change of a variable.
    watch_list_cp: WatchListCP,
    /// Contains information on which propagator to notify upon
    /// literal assignment. Not to be confused with the watch list
    /// of the clausal propagator.
    watch_list_propositional: WatchListPropositional,
    /// Used in combination with the propositional watch list
    /// Indicates the next literal on the propositional trail that need to be inspected to notify
    /// subscribed propagators.
    propositional_trail_index: usize,
    /// Dictates the order in which propagators will be called to propagate.
    propagator_queue: PropagatorQueue,
    /// Handles storing information about propagation reasons, which are used later to construct
    /// explanations during conflict analysis
    pub(crate) reason_store: ReasonStore,
    /// Contains events that need to be processed to notify propagators of [`IntDomainEvent`]
    /// occurrences.
    event_drain: Vec<(IntDomainEvent, DomainId)>,
    /// Holds information needed to map atomic constraints (e.g., [x >= 5]) to literals
    pub(crate) variable_literal_mappings: VariableLiteralMappings,
    /// Used during synchronisation of the propositional and integer trail.
    /// [`AssignmentsInteger::trail`][`cp_trail_synced_position`] is the next entry
    /// that needs to be synchronised with [`AssignmentsPropositional::trail`].
    cp_trail_synced_position: usize,
    /// This is the SAT equivalent of the above, i.e., [`AssignmentsPropositional::trail`]
    /// [[`sat_trail_synced_position`]] is the next
    /// [`Literal`] on the trail that needs to be synchronised with [`AssignmentsInteger::trail`].
    sat_trail_synced_position: usize,
    /// Holds information about explanations during conflict analysis.
    explanation_clause_manager: ExplanationClauseManager,
    /// Convenience literals used in special cases.
    true_literal: Literal,
    false_literal: Literal,
    /// A set of counters updated during the search.
    counters: Counters,
    /// Miscellaneous constant parameters used by the solver.
    internal_parameters: SatisfactionSolverOptions,
    /// The names of the variables in the solver.
    variable_names: VariableNames,

    semantic_minimiser: SemanticMinimiser,
    recursive_minimiser: RecursiveMinimiser,
}

impl Debug for ConstraintSatisfactionSolver {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let cp_propagators: Vec<_> = self
            .cp_propagators
            .iter()
            .map(|_| DebugDyn::from("Propagator"))
            .collect();
        f.debug_struct("ConstraintSatisfactionSolver")
            .field("state", &self.state)
            .field("assumptions", &self.assumptions)
            .field("clausal_allocator", &self.clause_allocator)
            .field("assignments_propositional", &self.assignments_propositional)
            .field("clausal_propagator", &self.clausal_propagator)
            .field("cp_propagators", &cp_propagators)
            .field("counters", &self.counters)
            .field("internal_parameters", &self.internal_parameters)
            .finish()
    }
}

impl Default for ConstraintSatisfactionSolver {
    fn default() -> Self {
        ConstraintSatisfactionSolver::new(SatisfactionSolverOptions::default())
    }
}

/// Options for the [`Solver`] which determine how it behaves.
#[derive(Debug)]
pub struct SatisfactionSolverOptions {
    /// A random generator which is used by the [`Solver`], passing it as an
    /// argument allows seeding of the randomization.
    pub random_generator: SmallRng,

    /// The strategy to use when the solver reaches a conflicting state.
    pub conflict_resolver: ConflictResolutionStrategy,

    pub minimisation_strategy: ClauseMinimisationStrategy,
}

/// The strategy used for minimisation
#[derive(Default, Clone, Copy, Debug, PartialEq, Eq, ValueEnum)]
pub enum ClauseMinimisationStrategy {
    #[default]
    NoMinimisation,
    /// Apply only recursive minimisation
    Recursive,
    /// Apply only semantic minimisation
    Semantic,
    /// First apply recursive minimisation and then apply semantic minimisation
    RecursiveSemantic,
    /// First apply semantic minimisation and then apply recursive minimisation
    SemanticRecursive,
}

impl Display for ClauseMinimisationStrategy {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ClauseMinimisationStrategy::NoMinimisation => write!(f, "no-minimisation"),
            ClauseMinimisationStrategy::Recursive => write!(f, "recursive"),
            ClauseMinimisationStrategy::Semantic => write!(f, "semantic"),
            ClauseMinimisationStrategy::RecursiveSemantic => write!(f, "recursive-semantic"),
            ClauseMinimisationStrategy::SemanticRecursive => write!(f, "semantic-recursive"),
        }
    }
}

/// The strategy used for conflict resolution.
#[derive(Default, Clone, Copy, Debug, PartialEq, Eq, ValueEnum)]
pub enum ConflictResolutionStrategy {
    UniqueImplicationPoint,
    AllDecision,
    #[default]
    NoLearning,
}

impl Display for ConflictResolutionStrategy {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ConflictResolutionStrategy::UniqueImplicationPoint => {
                write!(f, "unique-implication-point")
            }
            ConflictResolutionStrategy::AllDecision => write!(f, "all-decision"),
            ConflictResolutionStrategy::NoLearning => write!(f, "no-learning"),
        }
    }
}

impl ConflictResolutionStrategy {
    fn make(self) -> Box<dyn ConflictResolver> {
        match self {
            ConflictResolutionStrategy::UniqueImplicationPoint => {
                Box::new(UniqueImplicationPoint::default())
            }
            ConflictResolutionStrategy::AllDecision => Box::new(AllDecisionLearning::default()),
            ConflictResolutionStrategy::NoLearning => Box::new(NoLearning),
        }
    }
}

impl Default for SatisfactionSolverOptions {
    fn default() -> Self {
        SatisfactionSolverOptions {
            random_generator: SmallRng::seed_from_u64(42),
            conflict_resolver: ConflictResolutionStrategy::default(),
            minimisation_strategy: ClauseMinimisationStrategy::default(),
        }
    }
}

impl ConstraintSatisfactionSolver {
    /// Process the stored domain events. If no events were present, this returns false. Otherwise,
    /// true is returned.
    fn process_domain_events(&mut self) -> bool {
        // If there are no variables being watched then there is no reason to perform these
        // operations
        if self.watch_list_cp.is_watching_anything() {
            self.event_drain
                .extend(self.assignments_integer.drain_domain_events());

            if self.event_drain.is_empty()
                && self.propositional_trail_index
                    == self.assignments_propositional.num_trail_entries()
            {
                return false;
            }

            for (event, domain) in self.event_drain.drain(..) {
                for propagator_var in self.watch_list_cp.get_affected_propagators(event, domain) {
                    self.propagator_queue
                        .enqueue_propagator(propagator_var.propagator, 0);
                }
            }
        }
        // If there are no literals being watched then there is no reason to perform these
        // operations
        if self.watch_list_propositional.is_watching_anything() {
            for i in
                self.propositional_trail_index..self.assignments_propositional.num_trail_entries()
            {
                let literal = self.assignments_propositional.get_trail_entry(i);
                for (event, affected_literal) in BooleanDomainEvent::get_iterator(literal) {
                    for propagator_var in self
                        .watch_list_propositional
                        .get_affected_propagators(event, affected_literal)
                    {
                        self.propagator_queue
                            .enqueue_propagator(propagator_var.propagator, 0);
                    }
                }
            }
            self.propositional_trail_index = self.assignments_propositional.num_trail_entries();
        }

        true
    }

    /// Given a predicate, returns the corresponding literal.
    pub fn get_literal(&self, predicate: Predicate) -> Literal {
        match predicate {
            Predicate::IntegerPredicate(integer_predicate) => {
                self.variable_literal_mappings.get_literal(
                    integer_predicate,
                    &self.assignments_propositional,
                    &self.assignments_integer,
                )
            }
            bool_predicate => bool_predicate
                .get_literal_of_bool_predicate(self.assignments_propositional.true_literal)
                .unwrap(),
        }
    }

    /// This is a temporary accessor to help refactoring.
    pub fn get_solution_reference(&self) -> SolutionReference<'_> {
        SolutionReference::new(&self.assignments_propositional, &self.assignments_integer)
    }

    #[allow(unused)]
    pub(crate) fn is_conflicting(&self) -> bool {
        self.state.conflicting()
    }

    #[allow(unused)]
    pub(crate) fn declare_ready(&mut self) {
        self.state.declare_ready()
    }
}

// methods that offer basic functionality
impl ConstraintSatisfactionSolver {
    pub fn new(solver_options: SatisfactionSolverOptions) -> Self {
        let dummy_literal = Literal::new(PropositionalVariable::new(0), true);

        let mut csp_solver = ConstraintSatisfactionSolver {
            state: CSPSolverState::default(),
            assumptions: Vec::default(),
            assignments_propositional: AssignmentsPropositional::default(),
            clause_allocator: ClauseAllocator::default(),
            assignments_integer: AssignmentsInteger::default(),
            watch_list_cp: WatchListCP::default(),
            watch_list_propositional: WatchListPropositional::default(),
            propagator_queue: PropagatorQueue::new(5),
            reason_store: ReasonStore::default(),
            propositional_trail_index: 0,
            event_drain: vec![],
            variable_literal_mappings: VariableLiteralMappings::default(),
            cp_trail_synced_position: 0,
            sat_trail_synced_position: 0,
            explanation_clause_manager: ExplanationClauseManager::default(),
            true_literal: dummy_literal,
            false_literal: !dummy_literal,
            conflict_resolver: solver_options.conflict_resolver.make(),
            clausal_propagator: ClausalPropagator::default(),
            cp_propagators: vec![],
            counters: Counters::default(),
            internal_parameters: solver_options,
            variable_names: VariableNames::default(),
            semantic_minimiser: Default::default(),
            recursive_minimiser: Default::default(),
        };

        // we introduce a dummy variable set to true at the root level
        //  this is useful for convenience when a fact needs to be expressed that is always true
        //  e.g., this makes writing propagator explanations easier for corner cases
        let root_variable = csp_solver.create_new_propositional_variable(Some("true".to_owned()));
        let true_literal = Literal::new(root_variable, true);

        csp_solver.assignments_propositional.true_literal = true_literal;
        csp_solver.assignments_propositional.false_literal = !true_literal;

        csp_solver.true_literal = true_literal;
        csp_solver.false_literal = !true_literal;

        let result = csp_solver.add_clause([true_literal]);
        munchkin_assert_simple!(result.is_ok());

        csp_solver
    }

    pub fn solve(
        &mut self,
        termination: &mut impl TerminationCondition,
        brancher: &mut impl Brancher,
    ) -> CSPSolverExecutionFlag {
        let dummy_assumptions: Vec<Literal> = vec![];
        self.solve_under_assumptions(&dummy_assumptions, termination, brancher)
    }

    pub fn solve_under_assumptions(
        &mut self,
        assumptions: &[Literal],
        termination: &mut impl TerminationCondition,
        brancher: &mut impl Brancher,
    ) -> CSPSolverExecutionFlag {
        if self.state.is_inconsistent() {
            return CSPSolverExecutionFlag::Infeasible;
        }

        let start_time = Instant::now();

        self.initialise(assumptions);
        let result = self.solve_internal(termination, brancher);

        self.counters.time_spent_in_solver += start_time.elapsed().as_millis() as u64;

        result
    }

    pub fn log_statistics(&self) {
        self.counters.log_statistics()
    }

    /// Create a new integer variable. Its domain will have the given lower and upper bounds.
    pub fn create_new_integer_variable(
        &mut self,
        lower_bound: i32,
        upper_bound: i32,
        name: Option<String>,
    ) -> DomainId {
        assert!(
            !self.state.is_inconsistent(),
            "Variables cannot be created in an inconsistent state"
        );

        let domain = self.variable_literal_mappings.create_new_domain(
            lower_bound,
            upper_bound,
            &mut self.assignments_integer,
            &mut self.watch_list_cp,
            &mut self.watch_list_propositional,
            &mut self.clausal_propagator,
            &mut self.assignments_propositional,
            &mut self.clause_allocator,
        );

        if let Some(name) = name {
            self.variable_names.add_integer(domain, name);
        }

        domain
    }

    /// Creates an integer variable with a domain containing only the values in `values`
    pub fn create_new_integer_variable_sparse(
        &mut self,
        mut values: Vec<i32>,
        name: Option<String>,
    ) -> DomainId {
        assert!(
            !values.is_empty(),
            "cannot create a variable with an empty domain"
        );

        values.sort();
        values.dedup();

        let lower_bound = values[0];
        let upper_bound = values[values.len() - 1];

        let domain_id = self.create_new_integer_variable(lower_bound, upper_bound, name);

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

    /// Returns an infinite iterator of positive literals of new variables. The new variables will
    /// be unnamed.
    ///
    /// Note that this method captures the lifetime of the immutable reference to `self`.
    pub fn new_literals(&mut self) -> impl Iterator<Item = Literal> + '_ {
        std::iter::from_fn(|| Some(self.create_new_propositional_variable(None)))
            .map(|var| Literal::new(var, true))
    }

    pub fn create_new_propositional_variable(
        &mut self,
        name: Option<String>,
    ) -> PropositionalVariable {
        let variable = self
            .variable_literal_mappings
            .create_new_propositional_variable(
                &mut self.watch_list_propositional,
                &mut self.clausal_propagator,
                &mut self.assignments_propositional,
            );

        if let Some(name) = name {
            self.variable_names.add_propositional(variable, name);
        }

        variable
    }

    /// Get a literal which is globally true.
    pub fn get_true_literal(&self) -> Literal {
        self.assignments_propositional.true_literal
    }

    /// Get a literal which is globally false.
    pub fn get_false_literal(&self) -> Literal {
        self.assignments_propositional.false_literal
    }

    /// Get the lower bound for the given variable.
    pub fn get_lower_bound(&self, variable: &impl IntegerVariable) -> i32 {
        variable.lower_bound(&self.assignments_integer)
    }

    /// Get the upper bound for the given variable.
    pub fn get_upper_bound(&self, variable: &impl IntegerVariable) -> i32 {
        variable.upper_bound(&self.assignments_integer)
    }

    /// Determine whether `value` is in the domain of `variable`.
    pub fn integer_variable_contains(&self, variable: &impl IntegerVariable, value: i32) -> bool {
        variable.contains(&self.assignments_integer, value)
    }

    /// Get the assigned integer for the given variable. If it is not assigned, `None` is returned.
    pub fn get_assigned_integer_value(&self, variable: &impl IntegerVariable) -> Option<i32> {
        let lb = self.get_lower_bound(variable);
        let ub = self.get_upper_bound(variable);

        if lb == ub {
            Some(lb)
        } else {
            None
        }
    }

    /// Get the value of the given literal, which could be unassigned.
    pub fn get_literal_value(&self, literal: Literal) -> Option<bool> {
        if self.assignments_propositional.is_literal_assigned(literal) {
            Some(
                self.assignments_propositional
                    .is_literal_assigned_true(literal),
            )
        } else {
            None
        }
    }

    pub(crate) fn get_propositional_assignments(&self) -> &AssignmentsPropositional {
        &self.assignments_propositional
    }

    pub fn restore_state_at_root(&mut self, brancher: &mut impl Brancher) {
        if !self.assignments_propositional.is_at_the_root_level() {
            self.backtrack(0, brancher);
            self.state.declare_ready();
        }
    }

    fn synchronise_propositional_trail_based_on_integer_trail(&mut self) -> Option<ConflictInfo> {
        // for each entry on the integer trail, we now add the equivalent propositional
        // representation on the propositional trail  note that only one literal per
        // predicate will be stored      since the clausal propagator will propagate other
        // literals to ensure that the meaning of the literal is respected          e.g.,
        // placing [x >= 5] will prompt the clausal propagator to set [x >= 4] [x >= 3] ... [x >= 1]
        // to true
        for cp_trail_pos in
            self.cp_trail_synced_position..self.assignments_integer.num_trail_entries()
        {
            let entry = self.assignments_integer.get_trail_entry(cp_trail_pos);

            // It could be the case that the reason is `None`
            // due to a SAT propagation being put on the trail during
            // `synchronise_integer_trail_based_on_propositional_trail` In that case we
            // do not synchronise since we assume that the SAT trail is already aware of the
            // information
            if let Some(reason_ref) = entry.reason {
                let literal = self.variable_literal_mappings.get_literal(
                    entry.predicate,
                    &self.assignments_propositional,
                    &self.assignments_integer,
                );

                let constraint_reference = ConstraintReference::create_reason_reference(reason_ref);

                let conflict_info = self
                    .assignments_propositional
                    .enqueue_propagated_literal(literal, constraint_reference);

                if conflict_info.is_some() {
                    self.cp_trail_synced_position = cp_trail_pos + 1;
                    return conflict_info;
                }

                // It could occur that one of these propagations caused a conflict in which case the
                // SAT-view and the CP-view are unsynchronised We need to ensure
                // that the views are synchronised up to the CP trail entry which caused the
                // conflict
                if let Err(e) = self.clausal_propagator.propagate(
                    &mut self.assignments_propositional,
                    &mut self.clause_allocator,
                ) {
                    self.cp_trail_synced_position = cp_trail_pos + 1;
                    return Some(e);
                }
            }
        }
        self.cp_trail_synced_position = self.assignments_integer.num_trail_entries();
        None
    }

    fn synchronise_integer_trail_based_on_propositional_trail(
        &mut self,
    ) -> Result<(), EmptyDomain> {
        munchkin_assert_moderate!(
            self.cp_trail_synced_position == self.assignments_integer.num_trail_entries(),
            "We can only sychronise the propositional trail if the integer trail is already
             sychronised."
        );

        // this could possibly be improved if it shows up as a performance hotspot
        //  in some cases when we push e.g., [x >= a] on the stack, then we could also add the
        // literals to the propositional stack  and update the next_domain_trail_position
        // pointer to go pass the entries that surely are not going to lead to any changes
        //  this would only work if the next_domain_trail pointer is already at the end of the
        // stack, think about this, could be useful for propagators      and might be useful
        // for a custom domain propagator  this would also simplify the code below, no
        // additional checks would be needed? Not sure.

        if self.assignments_integer.num_domains() == 0 {
            self.sat_trail_synced_position = self.assignments_propositional.num_trail_entries();
            return Ok(());
        }

        for sat_trail_pos in
            self.sat_trail_synced_position..self.assignments_propositional.num_trail_entries()
        {
            let literal = self
                .assignments_propositional
                .get_trail_entry(sat_trail_pos);
            self.synchronise_literal(literal)?;
        }
        self.sat_trail_synced_position = self.assignments_propositional.num_trail_entries();
        // the newly added entries to the trail do not need to be synchronise with the propositional
        // trail  this is because the integer trail was already synchronise when this method
        // was called  and the newly added entries are already present on the propositional
        // trail
        self.cp_trail_synced_position = self.assignments_integer.num_trail_entries();

        let _ = self.process_domain_events();

        Ok(())
    }

    fn synchronise_literal(&mut self, literal: Literal) -> Result<(), EmptyDomain> {
        // recall that a literal may be linked to multiple predicates
        //  e.g., this may happen when in preprocessing two literals are detected to be equal
        //  so now we loop for each predicate and make necessary updates
        //  (although currently we do not have any serious preprocessing!)
        for j in 0..self.variable_literal_mappings.literal_to_predicates[literal].len() {
            let predicate = self.variable_literal_mappings.literal_to_predicates[literal][j];
            self.assignments_integer
                .apply_integer_predicate(predicate, None)?;
        }
        Ok(())
    }

    fn synchronise_assignments(&mut self) {
        munchkin_assert_simple!(
            self.sat_trail_synced_position >= self.assignments_propositional.num_trail_entries()
        );
        munchkin_assert_simple!(
            self.cp_trail_synced_position >= self.assignments_integer.num_trail_entries()
        );
        self.cp_trail_synced_position = self.assignments_integer.num_trail_entries();
        self.sat_trail_synced_position = self.assignments_propositional.num_trail_entries();
    }
}

// methods that serve as the main building blocks
impl ConstraintSatisfactionSolver {
    fn initialise(&mut self, assumptions: &[Literal]) {
        munchkin_assert_simple!(
            !self.state.is_infeasible_under_assumptions(),
            "Solver is not expected to be in the infeasible under assumptions state when initialising.
             Missed extracting the core?"
        );
        self.state.declare_solving();
        assumptions.clone_into(&mut self.assumptions);
    }

    fn solve_internal(
        &mut self,
        termination: &mut impl TerminationCondition,
        brancher: &mut impl Brancher,
    ) -> CSPSolverExecutionFlag {
        loop {
            self.propagate_enqueued(termination);

            if termination.should_stop() {
                self.state.declare_timeout();
                return CSPSolverExecutionFlag::Timeout;
            }

            if self.state.no_conflict() {
                self.declare_new_decision_level();

                let branching_result = self.enqueue_next_decision(brancher);
                if let Err(flag) = branching_result {
                    return flag;
                }
            } else {
                // Conflict has occured

                if self.assignments_propositional.is_at_the_root_level() {
                    // If it is at the root level then the problem is infeasible
                    self.state.declare_infeasible();
                    return CSPSolverExecutionFlag::Infeasible;
                }

                // Otherwise we resolve the conflict (and potentially learn a new clause)
                self.resolve_conflict(brancher);

                if self.state.is_inconsistent() {
                    return CSPSolverExecutionFlag::Infeasible;
                }

                brancher.on_conflict()
            }
        }
    }

    fn enqueue_next_decision(
        &mut self,
        brancher: &mut impl Brancher,
    ) -> Result<(), CSPSolverExecutionFlag> {
        if let Some(assumption_literal) = self.peek_next_assumption_literal() {
            let success = self.enqueue_assumption_literal(assumption_literal);
            if !success {
                return Err(CSPSolverExecutionFlag::Infeasible);
            }
            Ok(())
        } else {
            let decided_predicate = brancher.next_decision(&mut SelectionContext::new(
                &self.assignments_integer,
                &self.assignments_propositional,
                &mut self.internal_parameters.random_generator,
            ));
            if let Some(predicate) = decided_predicate {
                self.counters.num_decisions += 1;
                self.assignments_propositional
                    .enqueue_decision_literal(match predicate {
                        Predicate::IntegerPredicate(integer_predicate) => {
                            self.variable_literal_mappings.get_literal(
                                integer_predicate,
                                &self.assignments_propositional,
                                &self.assignments_integer,
                            )
                        }
                        bool_predicate => bool_predicate
                            .get_literal_of_bool_predicate(
                                self.assignments_propositional.true_literal,
                            )
                            .unwrap(),
                    });
                Ok(())
            } else {
                self.state.declare_solution_found();
                Err(CSPSolverExecutionFlag::Feasible)
            }
        }
    }

    /// Returns true if the assumption was successfully enqueued, and false otherwise
    pub(crate) fn enqueue_assumption_literal(&mut self, assumption_literal: Literal) -> bool {
        // Case 1: the assumption is unassigned, assign it
        if self
            .assignments_propositional
            .is_literal_unassigned(assumption_literal)
        {
            self.assignments_propositional
                .enqueue_decision_literal(assumption_literal);
            true
        // Case 2: the assumption has already been set to true
        //  this happens when other assumptions propagated the literal
        //  or the assumption is already set to true at the root level
        } else if self
            .assignments_propositional
            .is_literal_assigned_true(assumption_literal)
        {
            // in this case, do nothing
            //  note that the solver will then increase the decision level without enqueuing a
            // decision literal  this is necessary because by convention the solver will
            // try to assign the i-th assumption literal at decision level i+1
            true
        }
        // Case 3: the assumption literal is in conflict with the input assumption
        //  which means the instance is infeasible under the current assumptions
        else {
            self.state
                .declare_infeasible_under_assumptions(assumption_literal);
            false
        }
    }

    pub(crate) fn declare_new_decision_level(&mut self) {
        self.assignments_propositional.increase_decision_level();
        self.assignments_integer.increase_decision_level();
        self.reason_store.increase_decision_level();
    }

    fn minimise_learned_nogood(&mut self, learned_nogood: &mut LearnedNogood) {
        let num_literals_before = learned_nogood.literals.len();
        let context = MinimisationContext::new(
            &self.assignments_integer,
            &self.assignments_propositional,
            &self.variable_literal_mappings,
            &mut self.explanation_clause_manager,
            &mut self.reason_store,
            &self.clausal_propagator,
            &mut self.clause_allocator,
        );
        match self.internal_parameters.minimisation_strategy {
            ClauseMinimisationStrategy::NoMinimisation => {}
            ClauseMinimisationStrategy::Recursive => {
                self.recursive_minimiser.minimise(context, learned_nogood);
                self.counters
                    .average_number_of_literals_removed_recursive
                    .add_term((num_literals_before - learned_nogood.literals.len()) as u64);
            }
            ClauseMinimisationStrategy::Semantic => {
                self.semantic_minimiser.minimise(context, learned_nogood);
                self.counters
                    .average_number_of_literals_removed_semantic
                    .add_term((num_literals_before - learned_nogood.literals.len()) as u64);
            }
            ClauseMinimisationStrategy::RecursiveSemantic => {
                self.recursive_minimiser.minimise(context, learned_nogood);
                self.counters
                    .average_number_of_literals_removed_recursive
                    .add_term((num_literals_before - learned_nogood.literals.len()) as u64);
                let new_before = learned_nogood.literals.len();
                let context = MinimisationContext::new(
                    &self.assignments_integer,
                    &self.assignments_propositional,
                    &self.variable_literal_mappings,
                    &mut self.explanation_clause_manager,
                    &mut self.reason_store,
                    &self.clausal_propagator,
                    &mut self.clause_allocator,
                );
                self.semantic_minimiser.minimise(context, learned_nogood);
                self.counters
                    .average_number_of_literals_removed_semantic
                    .add_term((new_before - learned_nogood.literals.len()) as u64);
            }
            ClauseMinimisationStrategy::SemanticRecursive => {
                self.semantic_minimiser.minimise(context, learned_nogood);
                self.counters
                    .average_number_of_literals_removed_semantic
                    .add_term((num_literals_before - learned_nogood.literals.len()) as u64);
                let new_before = learned_nogood.literals.len();
                let context = MinimisationContext::new(
                    &self.assignments_integer,
                    &self.assignments_propositional,
                    &self.variable_literal_mappings,
                    &mut self.explanation_clause_manager,
                    &mut self.reason_store,
                    &self.clausal_propagator,
                    &mut self.clause_allocator,
                );
                self.recursive_minimiser.minimise(context, learned_nogood);
                self.counters
                    .average_number_of_literals_removed_recursive
                    .add_term((new_before - learned_nogood.literals.len()) as u64);
            }
        }
        self.counters
            .average_number_of_literals_removed_minimisation
            .add_term((num_literals_before - learned_nogood.literals.len()) as u64);

        recompute_invariants(
            PropagationContext::new(&self.assignments_integer, &self.assignments_propositional),
            learned_nogood,
        )
    }

    /// Changes the state based on the conflict analysis result (stored in
    /// [`ConstraintSatisfactionSolver::analysis_result`]). It performs the following:
    /// - Adds the learned clause to the database
    /// - Performs backtracking
    /// - Enqueues the propagated [`Literal`] of the learned clause
    /// - Updates the internal data structures (e.g. for the restart strategy or the learned clause
    ///   manager)
    ///
    /// # Note
    /// This method performs no propagation, this is left up to the solver afterwards
    fn resolve_conflict(&mut self, brancher: &mut impl Brancher) {
        munchkin_assert_moderate!(self.state.conflicting());

        let mut learned_nogood = self.compute_learned_nogood(brancher);
        // We calculate some statistics and perform clause minimisation (before collecting the
        // statistics)
        if let Some(learned_nogood) = learned_nogood.as_mut() {
            self.minimise_learned_nogood(learned_nogood);

            self.counters
                .average_learned_nogood_lbd
                .add_term(
                    calculate_lbd(&learned_nogood.literals, &self.assignments_propositional) as u64,
                );
            self.counters
                .average_backtrack_amount
                .add_term((self.get_decision_level() - learned_nogood.backjump_level) as u64);
            self.counters
                .average_learned_nogood_length
                .add_term(learned_nogood.literals.len() as u64);
            if learned_nogood.literals.len() == 1 {
                self.counters.num_unit_nogood_learned += 1;
            }
        }

        let result = self.process_learned_nogood(learned_nogood, brancher);

        if result.is_err() {
            self.state.declare_infeasible();
        } else {
            self.state.declare_solving();
        }
    }

    fn compute_learned_nogood(&mut self, brancher: &mut impl Brancher) -> Option<LearnedNogood> {
        let mut conflict_analysis_context = ConflictAnalysisContext {
            assumptions: &self.assumptions,
            clausal_propagator: &mut self.clausal_propagator,
            variable_literal_mappings: &self.variable_literal_mappings,
            assignments_integer: &mut self.assignments_integer,
            assignments_propositional: &mut self.assignments_propositional,
            internal_parameters: &self.internal_parameters,
            solver_state: &mut self.state,
            brancher,
            clause_allocator: &mut self.clause_allocator,
            explanation_clause_manager: &mut self.explanation_clause_manager,
            reason_store: &mut self.reason_store,
            counters: &mut self.counters,
            propositional_trail_index: &mut self.propositional_trail_index,
            propagator_queue: &mut self.propagator_queue,
            watch_list_cp: &mut self.watch_list_cp,
            sat_trail_synced_position: &mut self.sat_trail_synced_position,
            cp_trail_synced_position: &mut self.cp_trail_synced_position,
        };
        self.conflict_resolver
            .resolve_conflict(&mut conflict_analysis_context)
    }

    fn process_learned_nogood(
        &mut self,
        learned_nogood: Option<LearnedNogood>,
        brancher: &mut impl Brancher,
    ) -> Result<(), ()> {
        let mut conflict_analysis_context = ConflictAnalysisContext {
            assumptions: &self.assumptions,
            clausal_propagator: &mut self.clausal_propagator,
            variable_literal_mappings: &self.variable_literal_mappings,
            assignments_integer: &mut self.assignments_integer,
            assignments_propositional: &mut self.assignments_propositional,
            internal_parameters: &self.internal_parameters,
            solver_state: &mut self.state,
            brancher,
            clause_allocator: &mut self.clause_allocator,
            explanation_clause_manager: &mut self.explanation_clause_manager,
            reason_store: &mut self.reason_store,
            counters: &mut self.counters,
            propositional_trail_index: &mut self.propositional_trail_index,
            propagator_queue: &mut self.propagator_queue,
            watch_list_cp: &mut self.watch_list_cp,
            sat_trail_synced_position: &mut self.sat_trail_synced_position,
            cp_trail_synced_position: &mut self.cp_trail_synced_position,
        };

        self.conflict_resolver
            .process(learned_nogood, &mut conflict_analysis_context)
    }

    pub(crate) fn backtrack(&mut self, backtrack_level: usize, brancher: &mut impl Brancher) {
        munchkin_assert_simple!(backtrack_level < self.get_decision_level());

        let unassigned_literals = self.assignments_propositional.synchronise(backtrack_level);

        unassigned_literals.for_each(|literal| {
            brancher.on_unassign_literal(literal);
            // TODO: We should also backtrack on the integer variables here
        });

        self.clausal_propagator
            .synchronise(self.assignments_propositional.num_trail_entries());

        munchkin_assert_simple!(
            self.assignments_propositional.get_decision_level()
                < self.assignments_integer.get_decision_level(),
            "assignments_propositional must be backtracked _before_ CPEngineDataStructures"
        );
        self.propositional_trail_index = min(
            self.propositional_trail_index,
            self.assignments_propositional.num_trail_entries(),
        );
        self.assignments_integer
            .synchronise(backtrack_level)
            .iter()
            .for_each(|(domain_id, previous_value)| {
                brancher.on_unassign_integer(*domain_id, *previous_value)
            });

        self.reason_store.synchronise(backtrack_level);
        self.propagator_queue.clear();
        //  note that variable_literal_mappings sync should be called after the sat/cp data
        // structures backtrack
        self.synchronise_assignments();
    }

    /// Main propagation loop.
    pub(crate) fn propagate_enqueued(&mut self, termination: &mut impl TerminationCondition) {
        let num_trail_entries_before = self.assignments_integer.num_trail_entries();

        loop {
            if termination.should_stop() {
                break;
            }

            let conflict_info = self.synchronise_propositional_trail_based_on_integer_trail();

            if let Some(conflict_info) = conflict_info {
                // The previous propagation triggered an empty domain.
                self.state
                    .declare_conflict(conflict_info.try_into().unwrap());
                break;
            }

            let clausal_propagation_status = self.clausal_propagator.propagate(
                &mut self.assignments_propositional,
                &mut self.clause_allocator,
            );

            if let Err(conflict_info) = clausal_propagation_status {
                self.state
                    .declare_conflict(conflict_info.try_into().unwrap());
                break;
            }

            self.synchronise_integer_trail_based_on_propositional_trail()
                .expect("should not be an error");

            // ask propagators to propagate
            let propagation_status_one_step_cp = self.propagate_cp_one_step();

            match propagation_status_one_step_cp {
                PropagationStatusOneStepCP::PropagationHappened => {
                    // do nothing, the result will be that the clausal propagator will go next
                    //  recall that the idea is to always propagate simpler propagators before more
                    // complex ones  after a cp propagation was done one step,
                    // it is time to go to the clausal propagator
                }
                PropagationStatusOneStepCP::FixedPoint => {
                    break;
                }
                PropagationStatusOneStepCP::ConflictDetected { conflict_info } => {
                    let result = self.synchronise_propositional_trail_based_on_integer_trail();

                    // If the clausal propagator found a conflict during synchronisation then we
                    // want to use that conflict; if we do not use that conflict then it could be
                    // the case that there are literals in the conflict_info found by the CP
                    // propagator which are not assigned in the SAT-view (which leads to an error
                    // during conflict analysis)
                    self.state.declare_conflict(
                        result
                            .map(|ci| {
                                ci.try_into()
                                    .expect("this is not a ConflictInfo::Explanation")
                            })
                            .unwrap_or(conflict_info),
                    );
                    break;
                }
            } // end match
        }

        self.counters.num_conflicts += self.state.conflicting() as u64;

        self.counters.num_propagations +=
            self.assignments_integer.num_trail_entries() as u64 - num_trail_entries_before as u64;

        // Only check fixed point propagation if there was no reported conflict.
        munchkin_assert_extreme!(
            self.state.conflicting()
                || DebugHelper::debug_fixed_point_propagation(
                    &self.clausal_propagator,
                    &self.assignments_integer,
                    &self.assignments_propositional,
                    &self.clause_allocator,
                    &self.cp_propagators,
                )
        );
    }

    /// Performs propagation using propagators, stops after a propagator propagates at least one
    /// domain change. The idea is to go to the clausal propagator first before proceeding with
    /// other propagators, in line with the idea of propagating simpler propagators before more
    /// complex ones.
    fn propagate_cp_one_step(&mut self) -> PropagationStatusOneStepCP {
        if self.propagator_queue.is_empty() {
            return PropagationStatusOneStepCP::FixedPoint;
        }

        #[cfg(feature = "explanation-checks")]
        let num_trail_entries_before = self.assignments_integer.num_trail_entries();

        let propagator_id = self.propagator_queue.pop();
        let propagator = &mut self.cp_propagators[propagator_id.0 as usize];
        let context = PropagationContextMut::new(
            &mut self.assignments_integer,
            &mut self.reason_store,
            &mut self.assignments_propositional,
            propagator_id,
        );

        match propagator.propagate(context) {
            // An empty domain conflict will be caught by the clausal propagator.
            Err(Inconsistency::EmptyDomain) => PropagationStatusOneStepCP::PropagationHappened,

            // A propagator-specific reason for the current conflict.
            Err(Inconsistency::Other(conflict_info)) => {
                if let ConflictInfo::Explanation(ref propositional_conjunction) = conflict_info {
                    munchkin_assert_advanced!(DebugHelper::debug_reported_failure(
                        &self.assignments_integer,
                        &self.assignments_propositional,
                        &self.variable_literal_mappings,
                        propositional_conjunction,
                        propagator.as_ref(),
                        propagator_id,
                    ));
                }

                PropagationStatusOneStepCP::ConflictDetected {
                    conflict_info: conflict_info.into_stored(propagator_id),
                }
            }

            Ok(()) => {
                let _ = self.process_domain_events();
                #[cfg(feature = "explanation-checks")]
                assert!(
                    DebugHelper::debug_check_propagations(
                        num_trail_entries_before,
                        propagator_id,
                        &self.assignments_integer,
                        &self.assignments_propositional,
                        &self.variable_literal_mappings,
                        &mut self.reason_store,
                        &self.cp_propagators,
                    ),
                    "Inconsistency in explanation detected"
                );
                PropagationStatusOneStepCP::PropagationHappened
            }
        }
    }

    fn are_all_assumptions_assigned(&self) -> bool {
        self.assignments_propositional.get_decision_level() > self.assumptions.len()
    }

    fn peek_next_assumption_literal(&self) -> Option<Literal> {
        if self.are_all_assumptions_assigned() {
            None
        } else {
            // the convention is that at decision level i, the (i-1)th assumption is set
            //  note that the decision level is increased before calling branching hence the minus
            // one
            Some(self.assumptions[self.assignments_propositional.get_decision_level() - 1])
        }
    }
}

// methods for adding constraints (propagators and clauses)
impl ConstraintSatisfactionSolver {
    /// Add a clause (of at least length 2) which could later be deleted. Be mindful of the effect
    /// of this on learned clauses etc. if a solve call were to be invoked after adding a clause
    /// through this function.
    ///
    /// The clause is marked as 'learned'.
    #[allow(unused)]
    pub(crate) fn add_allocated_deletable_clause(
        &mut self,
        clause: Vec<Literal>,
    ) -> ClauseReference {
        self.clausal_propagator
            .add_clause_unchecked(clause, true, &mut self.clause_allocator)
            .unwrap()
    }

    /// Delete an allocated clause. Users of this method must ensure the state of the solver stays
    /// well-defined. In particular, if there are learned clauses derived through this clause, and
    /// it is removed, those learned clauses may no-longer be valid.
    #[allow(unused)]
    pub(crate) fn delete_allocated_clause(&mut self, reference: ClauseReference) -> Vec<Literal> {
        let clause = self.clause_allocator[reference]
            .get_literal_slice()
            .to_vec();

        self.clausal_propagator
            .remove_clause_from_consideration(&clause, reference);
        self.clause_allocator.delete_clause(reference);

        clause
    }

    /// Post a new propagator to the solver. If unsatisfiability can be immediately determined
    /// through propagation, this will return `false`. If not, this returns `true`.
    ///
    /// The caller should ensure the solver is in the root state before calling this, either
    /// because no call to [`Self::solve()`] has been made, or because
    /// [`Self::restore_state_at_root()`] was called.
    ///
    /// If the solver is already in a conflicting state, i.e. a previous call to this method
    /// already returned `false`, calling this again will not alter the solver in any way, and
    /// `false` will be returned again.
    pub fn add_propagator(
        &mut self,
        propagator_to_add: impl Propagator + 'static,
    ) -> Result<(), ConstraintOperationError> {
        if self.state.is_inconsistent() {
            return Err(ConstraintOperationError::InfeasiblePropagator);
        }

        let new_propagator_id = PropagatorId(self.cp_propagators.len() as u32);

        self.cp_propagators.push(Box::new(propagator_to_add));

        let new_propagator = &mut self.cp_propagators[new_propagator_id];

        let mut initialisation_context = PropagatorInitialisationContext::new(
            &mut self.watch_list_cp,
            &mut self.watch_list_propositional,
            new_propagator_id,
            &self.assignments_integer,
            &self.assignments_propositional,
        );

        let initialisation_status = new_propagator.initialise_at_root(&mut initialisation_context);

        if initialisation_status.is_err() {
            self.state.declare_infeasible();
            Err(ConstraintOperationError::InfeasiblePropagator)
        } else {
            self.propagator_queue
                .enqueue_propagator(new_propagator_id, 0);

            self.propagate_enqueued(&mut Indefinite);

            if self.state.no_conflict() {
                Ok(())
            } else {
                Err(ConstraintOperationError::InfeasiblePropagator)
            }
        }
    }

    /// Creates a clause from `literals` and adds it to the current formula.
    ///
    /// If the formula becomes trivially unsatisfiable, a [`ConstraintOperationError`] will be
    /// returned. Subsequent calls to this method will always return an error, and no
    /// modification of the solver will take place.
    pub fn add_clause(
        &mut self,
        literals: impl IntoIterator<Item = Literal>,
    ) -> Result<(), ConstraintOperationError> {
        munchkin_assert_moderate!(!self.state.is_infeasible_under_assumptions());
        munchkin_assert_moderate!(self.is_propagation_complete());

        if self.state.is_infeasible() {
            return Err(ConstraintOperationError::InfeasibleState);
        }

        let literals: Vec<Literal> = literals.into_iter().collect();

        let result = self.clausal_propagator.add_permanent_clause(
            literals,
            &mut self.assignments_propositional,
            &mut self.clause_allocator,
        );

        if result.is_err() {
            self.state.declare_infeasible();
            return Err(ConstraintOperationError::InfeasibleClause);
        }

        self.propagate_enqueued(&mut Indefinite);

        if self.state.is_infeasible() {
            self.state.declare_infeasible();
            return Err(ConstraintOperationError::InfeasibleClause);
        }

        Ok(())
    }
}

// methods for getting simple info out of the solver
impl ConstraintSatisfactionSolver {
    pub fn is_propagation_complete(&self) -> bool {
        self.clausal_propagator
            .is_propagation_complete(self.assignments_propositional.num_trail_entries())
            && self.propagator_queue.is_empty()
    }

    pub(crate) fn get_decision_level(&self) -> usize {
        munchkin_assert_moderate!(
            self.assignments_propositional.get_decision_level()
                == self.assignments_integer.get_decision_level()
        );
        self.assignments_propositional.get_decision_level()
    }
}

#[derive(Default, Debug, Copy, Clone)]
pub(crate) struct CumulativeMovingAverage {
    sum: u64,
    num_terms: u64,
}

impl CumulativeMovingAverage {
    #[allow(unused)]
    pub(crate) fn add_term(&mut self, new_term: u64) {
        self.sum += new_term;
        self.num_terms += 1
    }

    pub(crate) fn value(&self) -> f64 {
        if self.num_terms > 0 {
            (self.sum as f64) / (self.num_terms as f64)
        } else {
            0.0
        }
    }
}

/// Structure responsible for storing several statistics of the solving process of the
/// [`ConstraintSatisfactionSolver`].
#[derive(Default, Debug, Copy, Clone)]
pub(crate) struct Counters {
    pub(crate) num_decisions: u64,
    pub(crate) num_conflicts: u64,
    num_propagations: u64,
    time_spent_in_solver: u64,

    pub(crate) average_conflict_size: CumulativeMovingAverage,
    num_unit_nogood_learned: u64,
    average_learned_nogood_length: CumulativeMovingAverage,
    average_backtrack_amount: CumulativeMovingAverage,
    average_learned_nogood_lbd: CumulativeMovingAverage,

    average_number_of_literals_removed_semantic: CumulativeMovingAverage,
    average_number_of_literals_removed_recursive: CumulativeMovingAverage,
    average_number_of_literals_removed_minimisation: CumulativeMovingAverage,
}

impl Counters {
    fn log_statistics(&self) {
        log_statistic("numberOfDecisions", self.num_decisions);
        log_statistic("numberOfConflicts", self.num_conflicts);
        log_statistic("numberOfPropagations", self.num_propagations);
        log_statistic("timeSpentInSolverInMilliseconds", self.time_spent_in_solver);
        log_statistic(
            "averageBacktrackAmount",
            self.average_backtrack_amount.value(),
        );

        log_statistic(
            "averageSizeOfConflictExplanation",
            self.average_conflict_size.value(),
        );
        log_statistic("numberOfLearnedUnitNogoods", self.num_unit_nogood_learned);
        log_statistic(
            "averageLearnedNogoodLength",
            self.average_learned_nogood_length.value(),
        );
        log_statistic(
            "averageLearnedNogoodLbd",
            self.average_learned_nogood_lbd.value(),
        )
    }
}

#[derive(Default, Debug)]
enum CSPSolverStateInternal {
    #[default]
    Ready,
    Solving,
    ContainsSolution,
    Conflict {
        #[allow(unused)]
        conflict_info: StoredConflictInfo,
    },
    Infeasible,
    InfeasibleUnderAssumptions {
        #[allow(unused)]
        violated_assumption: Literal,
    },
    Timeout,
}

#[derive(Default, Debug)]
pub(crate) struct CSPSolverState {
    internal_state: CSPSolverStateInternal,
}

impl CSPSolverState {
    pub(crate) fn is_ready(&self) -> bool {
        matches!(self.internal_state, CSPSolverStateInternal::Ready)
    }

    pub(crate) fn no_conflict(&self) -> bool {
        !self.conflicting()
    }

    pub(crate) fn conflicting(&self) -> bool {
        matches!(
            self.internal_state,
            CSPSolverStateInternal::Conflict { conflict_info: _ }
        )
        // self.is_clausal_conflict() || self.is_cp_conflict()
    }

    pub(crate) fn is_infeasible(&self) -> bool {
        matches!(self.internal_state, CSPSolverStateInternal::Infeasible)
    }

    /// Determines whether the current state is inconsistent; i.e. whether it is conflicting,
    /// infeasible or infeasible under assumptions
    pub(crate) fn is_inconsistent(&self) -> bool {
        self.conflicting() || self.is_infeasible() || self.is_infeasible_under_assumptions()
    }

    pub(crate) fn is_infeasible_under_assumptions(&self) -> bool {
        matches!(
            self.internal_state,
            CSPSolverStateInternal::InfeasibleUnderAssumptions {
                violated_assumption: _
            }
        )
    }

    #[allow(unused)]
    pub(crate) fn get_violated_assumption(&self) -> Literal {
        if let CSPSolverStateInternal::InfeasibleUnderAssumptions {
            violated_assumption,
        } = self.internal_state
        {
            violated_assumption
        } else {
            panic!(
                "Cannot extract violated assumption without getting the solver into the infeasible
                 under assumptions state."
            );
        }
    }

    #[allow(unused)]
    pub(crate) fn get_conflict_info(&self) -> &StoredConflictInfo {
        if let CSPSolverStateInternal::Conflict { conflict_info } = &self.internal_state {
            conflict_info
        } else {
            panic!("Cannot extract conflict clause if solver is not in a clausal conflict.");
        }
    }

    #[allow(unused)]
    pub(crate) fn timeout(&self) -> bool {
        matches!(self.internal_state, CSPSolverStateInternal::Timeout)
    }

    #[allow(unused)]
    pub(crate) fn has_solution(&self) -> bool {
        matches!(
            self.internal_state,
            CSPSolverStateInternal::ContainsSolution
        )
    }

    pub(crate) fn declare_ready(&mut self) {
        self.internal_state = CSPSolverStateInternal::Ready;
    }

    pub(crate) fn declare_solving(&mut self) {
        munchkin_assert_simple!((self.is_ready() || self.conflicting()) && !self.is_infeasible());
        self.internal_state = CSPSolverStateInternal::Solving;
    }

    fn declare_infeasible(&mut self) {
        self.internal_state = CSPSolverStateInternal::Infeasible;
    }

    pub(crate) fn declare_conflict(&mut self, conflict_info: StoredConflictInfo) {
        munchkin_assert_simple!(!self.conflicting());
        self.internal_state = CSPSolverStateInternal::Conflict { conflict_info };
    }

    fn declare_solution_found(&mut self) {
        munchkin_assert_simple!(!self.is_infeasible());
        self.internal_state = CSPSolverStateInternal::ContainsSolution;
    }

    fn declare_timeout(&mut self) {
        munchkin_assert_simple!(!self.is_infeasible());
        self.internal_state = CSPSolverStateInternal::Timeout;
    }

    fn declare_infeasible_under_assumptions(&mut self, violated_assumption: Literal) {
        munchkin_assert_simple!(!self.is_infeasible());
        self.internal_state = CSPSolverStateInternal::InfeasibleUnderAssumptions {
            violated_assumption,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::ConstraintSatisfactionSolver;
    use crate::engine::cp::reason::ReasonRef;
    use crate::predicate;

    #[test]
    fn negative_upper_bound() {
        let mut solver = ConstraintSatisfactionSolver::default();
        let domain_id = solver.create_new_integer_variable(0, 10, None);

        let result = solver.get_literal(predicate![domain_id <= -2]);
        assert_eq!(result, solver.assignments_propositional.false_literal);
    }

    #[test]
    fn lower_bound_literal_lower_than_lower_bound_should_be_true_literal() {
        let mut solver = ConstraintSatisfactionSolver::default();
        let domain_id = solver.create_new_integer_variable(0, 10, None);
        let result = solver.get_literal(predicate![domain_id >= -2]);
        assert_eq!(result, solver.assignments_propositional.true_literal);
    }

    #[test]
    fn new_domain_with_negative_lower_bound() {
        let lb = -2;
        let ub = 2;

        let mut solver = ConstraintSatisfactionSolver::default();
        let domain_id = solver.create_new_integer_variable(lb, ub, None);

        assert_eq!(lb, solver.assignments_integer.get_lower_bound(domain_id));

        assert_eq!(ub, solver.assignments_integer.get_upper_bound(domain_id));

        assert_eq!(
            solver.assignments_propositional.true_literal,
            solver.get_literal(predicate![domain_id >= lb])
        );

        assert_eq!(
            solver.assignments_propositional.false_literal,
            solver.get_literal(predicate![domain_id <= lb - 1])
        );

        assert!(solver
            .assignments_propositional
            .is_literal_unassigned(solver.get_literal(predicate![domain_id == lb])));

        assert_eq!(
            solver.assignments_propositional.false_literal,
            solver.get_literal(predicate![domain_id == lb - 1])
        );

        for value in (lb + 1)..ub {
            let literal = solver.get_literal(predicate![domain_id >= value]);

            assert!(solver
                .assignments_propositional
                .is_literal_unassigned(literal));

            assert!(solver
                .assignments_propositional
                .is_literal_unassigned(solver.get_literal(predicate![domain_id == value])));
        }

        assert_eq!(
            solver.assignments_propositional.false_literal,
            solver.get_literal(predicate![domain_id >= ub + 1])
        );
        assert_eq!(
            solver.assignments_propositional.true_literal,
            solver.get_literal(predicate![domain_id <= ub])
        );
        assert!(solver
            .assignments_propositional
            .is_literal_unassigned(solver.get_literal(predicate![domain_id == ub])));
        assert_eq!(
            solver.assignments_propositional.false_literal,
            solver.get_literal(predicate![domain_id == ub + 1])
        );
    }

    #[test]
    fn clausal_propagation_is_synced_until_right_before_conflict() {
        let mut solver = ConstraintSatisfactionSolver::default();
        let domain_id = solver.create_new_integer_variable(0, 10, None);
        let dummy_reason = ReasonRef(0);

        let result =
            solver
                .assignments_integer
                .tighten_lower_bound(domain_id, 2, Some(dummy_reason));
        assert!(result.is_ok());
        assert_eq!(solver.assignments_integer.get_lower_bound(domain_id), 2);

        let result =
            solver
                .assignments_integer
                .tighten_lower_bound(domain_id, 8, Some(dummy_reason));
        assert!(result.is_ok());
        assert_eq!(solver.assignments_integer.get_lower_bound(domain_id), 8);

        let result =
            solver
                .assignments_integer
                .tighten_lower_bound(domain_id, 12, Some(dummy_reason));
        assert!(result.is_err());
        assert_eq!(solver.assignments_integer.get_lower_bound(domain_id), 12);

        let _ = solver.synchronise_propositional_trail_based_on_integer_trail();

        for lower_bound in 0..=8 {
            let literal = solver.get_literal(predicate!(domain_id >= lower_bound));
            assert!(
                solver
                    .assignments_propositional
                    .is_literal_assigned_true(literal),
                "Literal for lower-bound {lower_bound} is not assigned"
            );
        }
    }

    #[test]
    fn check_correspondence_predicates_creating_new_int_domain() {
        let mut solver = ConstraintSatisfactionSolver::default();

        let lower_bound = 0;
        let upper_bound = 10;
        let domain_id = solver.create_new_integer_variable(lower_bound, upper_bound, None);

        for bound in lower_bound + 1..upper_bound {
            let lower_bound_predicate = predicate![domain_id >= bound];
            let equality_predicate = predicate![domain_id == bound];
            for predicate in [lower_bound_predicate, equality_predicate] {
                let literal = solver.get_literal(predicate);
                assert!(
                    solver.variable_literal_mappings.literal_to_predicates[literal]
                        .contains(&predicate.try_into().unwrap())
                )
            }
        }
    }
}
