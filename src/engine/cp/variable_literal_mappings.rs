//! Used to create propositional and integer variables. Holds information about mapping literals
//! to predicates (atomic constraints) and vice versa.
//!
//! Note that when integer variables are created, the solver also creates propositional variables
//! corresponding to atomic constraints (predicates).

use crate::basic_types::KeyedVec;
use crate::basic_types::StorageKey;
use crate::engine::cp::AssignmentsInteger;
use crate::engine::cp::WatchListCP;
use crate::engine::cp::WatchListPropositional;
use crate::engine::predicates::integer_predicate::IntegerPredicate;
use crate::engine::sat::AssignmentsPropositional;
use crate::engine::sat::ClausalPropagator;
use crate::engine::sat::ClauseAllocator;
use crate::engine::variables::DomainId;
use crate::engine::variables::Literal;
use crate::engine::variables::PropositionalVariable;
use crate::munchkin_assert_eq_simple;
use crate::munchkin_assert_simple;
use crate::predicate;

#[derive(Debug, Default)]
pub(crate) struct VariableLiteralMappings {
    /// `domain_to_equality_literals[DomainId x][i]` is the [`Literal`]
    /// that represents `[x == i + initial_lb(x)]`, where `initial_lb(x)` is
    /// the lower bound of [`DomainId`] `x` at the time of its creation.
    pub(crate) domain_to_equality_literals: KeyedVec<DomainId, Box<[Literal]>>,
    /// `domain_to_lower_bound_literals[DomainId x][i]` is the [`Literal`]
    /// that represents `[x >= i + initial_lb(x)]`, where `initial_lb(x)` is
    /// the lower bound of [`DomainId`] `x` at the time of its creation.
    /// Note that the [`Literal`]s representing `[x <= k]` are obtained by negating `[x >= k+1]`.
    pub(crate) domain_to_lower_bound_literals: KeyedVec<DomainId, Box<[Literal]>>,
    /// `literal_to_predicates[literal]` is the vector of [`IntegerPredicate`]s associated with
    /// the `literal`. Usually there are one or two [`IntegerPredicate`]s associated with a
    /// [`Literal`], but due to preprocessing (not currently implemented), it could be that one
    /// [`Literal`] is associated with three or more [`IntegerPredicate`]s.
    pub(crate) literal_to_predicates: KeyedVec<Literal, Vec<IntegerPredicate>>,
}

// methods for creating new variables
impl VariableLiteralMappings {
    /// Creates a new propositional literals, and registers the variable to the given predicate.
    ///
    /// Note that this function does not guarantee that the literal is appropriately propagated
    /// depending on the predicate. This function merely established a link in the internal data
    /// structures.
    fn create_new_propositional_variable_with_predicate(
        &mut self,
        watch_list_propositional: &mut WatchListPropositional,
        predicate: IntegerPredicate,
        clausal_propagator: &mut ClausalPropagator,
        assignments_propositional: &mut AssignmentsPropositional,
    ) -> PropositionalVariable {
        let variable = self.create_new_propositional_variable(
            watch_list_propositional,
            clausal_propagator,
            assignments_propositional,
        );
        self.add_predicate_information_to_propositional_variable(
            Literal::new(variable, true),
            predicate,
        );
        variable
    }

    /// Creates a new propositional variables.
    ///
    /// Note that the variable is not registered with any predicate.
    pub(crate) fn create_new_propositional_variable(
        &mut self,
        watch_list_propositional: &mut WatchListPropositional,
        clausal_propagator: &mut ClausalPropagator,
        assignments_propositional: &mut AssignmentsPropositional,
    ) -> PropositionalVariable {
        let new_variable_index = assignments_propositional.num_propositional_variables();

        clausal_propagator.grow();

        watch_list_propositional.grow();

        assignments_propositional.grow();

        // add an empty predicate vector for both polarities of the variable
        self.literal_to_predicates.push(vec![]);
        self.literal_to_predicates.push(vec![]);

        PropositionalVariable::new(new_variable_index)
    }

    /// Create a new integer variable and tie it to a fresh propositional representation. The given
    /// clausal propagator will be responsible for keeping the propositional representation
    /// consistent.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn create_new_domain(
        &mut self,
        lower_bound: i32,
        upper_bound: i32,
        assignments_integer: &mut AssignmentsInteger,
        watch_list_cp: &mut WatchListCP,
        watch_list_propositional: &mut WatchListPropositional,
        clausal_propagator: &mut ClausalPropagator,
        assignments_propositional: &mut AssignmentsPropositional,
        clause_allocator: &mut ClauseAllocator,
    ) -> DomainId {
        munchkin_assert_simple!(lower_bound <= upper_bound, "Inconsistent bounds.");
        // munchkin_assert_simple!(self.debug_check_consistency(cp_data_structures));

        // 1. Create the integer/domain representation.
        let domain_id = assignments_integer.grow(lower_bound, upper_bound);
        watch_list_cp.grow();

        // 2. Create the propositional representation.
        self.create_propositional_representation(
            domain_id,
            assignments_integer,
            watch_list_propositional,
            clausal_propagator,
            assignments_propositional,
            clause_allocator,
        );

        domain_id
    }

    /// Eagerly create the propositional representation of the integer variable. This is done using
    /// a unary representation.
    fn create_propositional_representation(
        &mut self,
        domain_id: DomainId,
        assignments_integer: &AssignmentsInteger,
        watch_list_propositional: &mut WatchListPropositional,
        clausal_propagator: &mut ClausalPropagator,
        assignments_propositional: &mut AssignmentsPropositional,
        clause_allocator: &mut ClauseAllocator,
    ) {
        let lower_bound_literals = self.create_lower_bound_literals(
            domain_id,
            assignments_integer,
            watch_list_propositional,
            clausal_propagator,
            assignments_propositional,
            clause_allocator,
        );

        let equality_literals = self.create_equality_literals(
            domain_id,
            &lower_bound_literals,
            assignments_integer,
            watch_list_propositional,
            clausal_propagator,
            assignments_propositional,
            clause_allocator,
        );

        self.domain_to_lower_bound_literals
            .push(lower_bound_literals);

        self.domain_to_equality_literals
            .push(equality_literals.clone());

        // Add clause to select at least one equality.
        clausal_propagator
            .add_permanent_clause(
                equality_literals.into(),
                assignments_propositional,
                clause_allocator,
            )
            .expect("at least one equality must hold");
    }

    /// Create the literals representing [x == v] for all values v in the initial domain.
    #[allow(clippy::too_many_arguments)]
    fn create_equality_literals(
        &mut self,
        domain_id: DomainId,
        lower_bound_literals: &[Literal],
        assignments_integer: &AssignmentsInteger,
        watch_list_propositional: &mut WatchListPropositional,
        clausal_propagator: &mut ClausalPropagator,
        assignments_propositional: &mut AssignmentsPropositional,
        clause_allocator: &mut ClauseAllocator,
    ) -> Box<[Literal]> {
        assert!(
            lower_bound_literals.len() >= 2,
            "the lower bound literals should contain at least two literals"
        );

        let lower_bound = assignments_integer.get_lower_bound(domain_id);
        let upper_bound = assignments_integer.get_upper_bound(domain_id);

        // The literal at index i is [x == lb(x) + i].
        let mut equality_literals: Vec<Literal> = Vec::new();

        // Edge case where i = 0: [x == lb(x)] <-> ~[x >= lb(x) + 1]
        equality_literals.push(!lower_bound_literals[1]);

        // Add the predicate information to the [x == lower_bound] literal.
        //
        // Because the predicates are attached to propositional variables (which we treat as true
        // literals), we have to be mindful of the polarity of the predicate.
        self.add_predicate_information_to_propositional_variable(
            equality_literals[0],
            predicate![domain_id == lower_bound].try_into().unwrap(),
        );

        for value in (lower_bound + 1)..upper_bound {
            let propositional_variable = self.create_new_propositional_variable_with_predicate(
                watch_list_propositional,
                predicate![domain_id == value].try_into().unwrap(),
                clausal_propagator,
                assignments_propositional,
            );

            equality_literals.push(Literal::new(propositional_variable, true));
        }

        if lower_bound < upper_bound {
            assert!(lower_bound_literals.last().unwrap().index() == 0);

            // Edge case [x == ub(x)] <-> [x >= ub(x)].
            // Note the -2: this is because the last literal
            // is reserved for a trivially false literal.
            let equals_ub = lower_bound_literals[lower_bound_literals.len() - 2];
            equality_literals.push(equals_ub);
            self.add_predicate_information_to_propositional_variable(
                equals_ub,
                predicate![domain_id == upper_bound].try_into().unwrap(),
            );
        }

        munchkin_assert_eq_simple!(
            equality_literals.len(),
            (upper_bound - lower_bound + 1) as usize
        );

        // Enforce consistency of the equality literals through the following clauses:
        // [x == value] <-> [x >= value] AND ~[x >= value + 1]
        //
        // The equality literals for the bounds are skipped, as they are already defined above.
        for value in (lower_bound + 1)..upper_bound {
            let idx = value.abs_diff(lower_bound) as usize;

            // One side of the implication <-
            clausal_propagator.add_permanent_ternary_clause_unchecked(
                !lower_bound_literals[idx],
                lower_bound_literals[idx + 1],
                equality_literals[idx],
                clause_allocator,
            );

            // The other side of the implication ->
            clausal_propagator.add_permanent_implication_unchecked(
                equality_literals[idx],
                lower_bound_literals[idx],
                clause_allocator,
            );

            clausal_propagator.add_permanent_implication_unchecked(
                equality_literals[idx],
                !lower_bound_literals[idx + 1],
                clause_allocator,
            );
        }

        equality_literals.into()
    }

    /// Eagerly create the literals that encode the bounds of the integer variable.
    #[allow(clippy::too_many_arguments)]
    fn create_lower_bound_literals(
        &mut self,
        domain_id: DomainId,
        assignments_integer: &AssignmentsInteger,
        watch_list_propositional: &mut WatchListPropositional,
        clausal_propagator: &mut ClausalPropagator,
        assignments_propositional: &mut AssignmentsPropositional,
        clause_allocator: &mut ClauseAllocator,
    ) -> Box<[Literal]> {
        let lower_bound = assignments_integer.get_lower_bound(domain_id);
        let upper_bound = assignments_integer.get_upper_bound(domain_id);

        // The literal at index i is [x >= lb(x) + i].
        let mut lower_bound_literals = Vec::new();

        // The integer variable will always be at least the lower bound of the initial domain.
        lower_bound_literals.push(assignments_propositional.true_literal);
        self.add_predicate_information_to_propositional_variable(
            lower_bound_literals[0],
            predicate![domain_id >= lower_bound].try_into().unwrap(),
        );

        for value in (lower_bound + 1)..=upper_bound {
            let propositional_variable = self.create_new_propositional_variable_with_predicate(
                watch_list_propositional,
                predicate![domain_id >= value].try_into().unwrap(),
                clausal_propagator,
                assignments_propositional,
            );

            lower_bound_literals.push(Literal::new(propositional_variable, true));
        }

        // The integer variable is never bigger than the upper bound of the initial domain.
        lower_bound_literals.push(assignments_propositional.false_literal);
        self.add_predicate_information_to_propositional_variable(
            lower_bound_literals.last().copied().unwrap(),
            predicate![domain_id >= upper_bound + 1].try_into().unwrap(),
        );

        munchkin_assert_eq_simple!(
            lower_bound_literals.len(),
            (upper_bound - lower_bound + 2) as usize
        );

        // Enforce consistency over the lower bound literals by adding the following clause:
        // [x >= v + 1] -> [x >= v].
        //
        // Special case (skipped in the loop): [x >= lb(x) + 1] -> [x >= lb(x)], but
        // [x >= lb(x)] is trivially true.
        for v in (lower_bound + 2)..=upper_bound {
            let idx = v.abs_diff(lower_bound) as usize;

            clausal_propagator.add_permanent_implication_unchecked(
                lower_bound_literals[idx],
                lower_bound_literals[idx - 1],
                clause_allocator,
            );
        }

        lower_bound_literals.into()
    }

    fn add_predicate_information_to_propositional_variable(
        &mut self,
        literal: Literal,
        predicate: IntegerPredicate,
    ) {
        munchkin_assert_simple!(
            (!literal).index() >= self.literal_to_predicates.len()
                || !self.literal_to_predicates[!literal].contains(&predicate),
            "The predicate is already attached to the _negative_ literal, cannot do this twice."
        );

        self.literal_to_predicates.accomodate(literal, vec![]);
        self.literal_to_predicates.accomodate(!literal, vec![]);

        self.literal_to_predicates[literal].push(predicate);
        self.literal_to_predicates[!literal].push(!predicate);
    }
}

// methods for getting simple information on the interface of SAT and CP
impl VariableLiteralMappings {
    /// Returns the [`DomainId`] of the first [`IntegerPredicate`] which the provided `literal` is
    /// linked to or [`None`] if no such [`DomainId`] exists.
    #[allow(unused, reason = "can be used in assignment")]
    pub(crate) fn get_domain_literal(&self, literal: Literal) -> Option<DomainId> {
        self.literal_to_predicates[literal]
            .first()
            .map(|predicate| predicate.get_domain())
    }

    ///  Returns a literal which corresponds to the provided [`IntegerPredicate`].
    pub(crate) fn get_literal(
        &self,
        predicate: IntegerPredicate,
        assignments_propositional: &AssignmentsPropositional,
        assignments_integer: &AssignmentsInteger,
    ) -> Literal {
        match predicate {
            IntegerPredicate::LowerBound {
                domain_id,
                lower_bound,
            } => self.get_lower_bound_literal(
                domain_id,
                lower_bound,
                assignments_propositional,
                assignments_integer,
            ),
            IntegerPredicate::UpperBound {
                domain_id,
                upper_bound,
            } => self.get_upper_bound_literal(
                domain_id,
                upper_bound,
                assignments_propositional,
                assignments_integer,
            ),
            IntegerPredicate::NotEqual {
                domain_id,
                not_equal_constant,
            } => self.get_inequality_literal(
                domain_id,
                not_equal_constant,
                assignments_propositional,
                assignments_integer,
            ),
            IntegerPredicate::Equal {
                domain_id,
                equality_constant,
            } => self.get_equality_literal(
                domain_id,
                equality_constant,
                assignments_propositional,
                assignments_integer,
            ),
        }
    }

    pub(crate) fn get_lower_bound_literal(
        &self,
        domain: DomainId,
        lower_bound: i32,
        assignments_propositional: &AssignmentsPropositional,
        assignments_integer: &AssignmentsInteger,
    ) -> Literal {
        let initial_lower_bound = assignments_integer.get_initial_lower_bound(domain);
        let initial_upper_bound = assignments_integer.get_initial_upper_bound(domain);

        if lower_bound < initial_lower_bound {
            return assignments_propositional.true_literal;
        }

        if lower_bound > initial_upper_bound {
            return assignments_propositional.false_literal;
        }

        let literal_idx = lower_bound.abs_diff(initial_lower_bound) as usize;
        self.domain_to_lower_bound_literals[domain][literal_idx]
    }

    pub(crate) fn get_upper_bound_literal(
        &self,
        domain: DomainId,
        upper_bound: i32,
        assignments_propositional: &AssignmentsPropositional,
        assignments_integer: &AssignmentsInteger,
    ) -> Literal {
        !self.get_lower_bound_literal(
            domain,
            upper_bound + 1,
            assignments_propositional,
            assignments_integer,
        )
    }

    pub(crate) fn get_equality_literal(
        &self,
        domain: DomainId,
        equality_constant: i32,
        assignments_propositional: &AssignmentsPropositional,
        assignments_integer: &AssignmentsInteger,
    ) -> Literal {
        let initial_lower_bound = assignments_integer.get_initial_lower_bound(domain);
        let initial_upper_bound = assignments_integer.get_initial_upper_bound(domain);

        if equality_constant < initial_lower_bound || equality_constant > initial_upper_bound {
            return assignments_propositional.false_literal;
        }

        let literal_idx = equality_constant.abs_diff(initial_lower_bound) as usize;
        self.domain_to_equality_literals[domain][literal_idx]
    }

    pub(crate) fn get_inequality_literal(
        &self,
        domain: DomainId,
        not_equal_constant: i32,
        assignments_propositional: &AssignmentsPropositional,
        assignments_integer: &AssignmentsInteger,
    ) -> Literal {
        !self.get_equality_literal(
            domain,
            not_equal_constant,
            assignments_propositional,
            assignments_integer,
        )
    }

    #[allow(unused, reason = "will be used in the assignments")]
    pub(crate) fn get_predicates_for_literal(
        &self,
        literal: Literal,
    ) -> impl Iterator<Item = IntegerPredicate> + '_ {
        self.literal_to_predicates[literal].iter().copied()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::predicate;

    #[test]
    fn negative_upper_bound() {
        let mut variable_literal_mappings = VariableLiteralMappings::default();
        let mut assignments_integer = AssignmentsInteger::default();
        let mut watch_list_cp = WatchListCP::default();
        let mut watch_list_propositional = WatchListPropositional::default();
        let mut clausal_propagator = ClausalPropagator::default();
        let mut assignments_propositional = AssignmentsPropositional::default();
        let mut clausal_allocator = ClauseAllocator::default();

        let domain_id = variable_literal_mappings.create_new_domain(
            0,
            10,
            &mut assignments_integer,
            &mut watch_list_cp,
            &mut watch_list_propositional,
            &mut clausal_propagator,
            &mut assignments_propositional,
            &mut clausal_allocator,
        );

        let result = variable_literal_mappings.get_upper_bound_literal(
            domain_id,
            -2,
            &assignments_propositional,
            &assignments_integer,
        );

        assert_eq!(result, assignments_propositional.false_literal);
    }

    #[test]
    fn lower_bound_literal_lower_than_lower_bound_should_be_true_literal() {
        let mut variable_literal_mappings = VariableLiteralMappings::default();
        let mut assignments_integer = AssignmentsInteger::default();
        let mut watch_list_cp = WatchListCP::default();
        let mut watch_list_propositional = WatchListPropositional::default();
        let mut clausal_propagator = ClausalPropagator::default();
        let mut assignments_propositional = AssignmentsPropositional::default();
        let mut clausal_allocator = ClauseAllocator::default();

        let domain_id = variable_literal_mappings.create_new_domain(
            0,
            10,
            &mut assignments_integer,
            &mut watch_list_cp,
            &mut watch_list_propositional,
            &mut clausal_propagator,
            &mut assignments_propositional,
            &mut clausal_allocator,
        );
        let result = variable_literal_mappings.get_lower_bound_literal(
            domain_id,
            -2,
            &assignments_propositional,
            &assignments_integer,
        );
        assert_eq!(result, assignments_propositional.true_literal);
    }

    #[test]
    fn new_domain_with_negative_lower_bound() {
        let mut variable_literal_mappings = VariableLiteralMappings::default();
        let mut assignments_integer = AssignmentsInteger::default();
        let mut watch_list_cp = WatchListCP::default();
        let mut watch_list_propositional = WatchListPropositional::default();
        let mut clausal_propagator = ClausalPropagator::default();
        let mut assignments_propositional = AssignmentsPropositional::default();
        let mut clausal_allocator = ClauseAllocator::default();

        let lb = -2;
        let ub = 2;

        let domain_id = variable_literal_mappings.create_new_domain(
            lb,
            ub,
            &mut assignments_integer,
            &mut watch_list_cp,
            &mut watch_list_propositional,
            &mut clausal_propagator,
            &mut assignments_propositional,
            &mut clausal_allocator,
        );

        assert_eq!(lb, assignments_integer.get_lower_bound(domain_id));
        assert_eq!(ub, assignments_integer.get_upper_bound(domain_id));

        assert_eq!(
            assignments_propositional.true_literal,
            variable_literal_mappings.get_lower_bound_literal(
                domain_id,
                lb,
                &assignments_propositional,
                &assignments_integer,
            )
        );

        assert_eq!(
            assignments_propositional.false_literal,
            variable_literal_mappings.get_upper_bound_literal(
                domain_id,
                lb - 1,
                &assignments_propositional,
                &assignments_integer,
            )
        );

        assert!(assignments_propositional.is_literal_unassigned(
            variable_literal_mappings.get_equality_literal(
                domain_id,
                lb,
                &assignments_propositional,
                &assignments_integer,
            )
        ));

        assert_eq!(
            assignments_propositional.false_literal,
            variable_literal_mappings.get_equality_literal(
                domain_id,
                lb - 1,
                &assignments_propositional,
                &assignments_integer,
            )
        );

        for value in (lb + 1)..ub {
            let literal = variable_literal_mappings.get_lower_bound_literal(
                domain_id,
                value,
                &assignments_propositional,
                &assignments_integer,
            );

            assert!(assignments_propositional.is_literal_unassigned(literal));

            assert!(assignments_propositional.is_literal_unassigned(
                variable_literal_mappings.get_equality_literal(
                    domain_id,
                    value,
                    &assignments_propositional,
                    &assignments_integer,
                )
            ));
        }

        assert_eq!(
            assignments_propositional.false_literal,
            variable_literal_mappings.get_lower_bound_literal(
                domain_id,
                ub + 1,
                &assignments_propositional,
                &assignments_integer,
            )
        );
        assert_eq!(
            assignments_propositional.true_literal,
            variable_literal_mappings.get_upper_bound_literal(
                domain_id,
                ub,
                &assignments_propositional,
                &assignments_integer,
            )
        );
        assert!(assignments_propositional.is_literal_unassigned(
            variable_literal_mappings.get_equality_literal(
                domain_id,
                ub,
                &assignments_propositional,
                &assignments_integer,
            )
        ));
        assert_eq!(
            assignments_propositional.false_literal,
            variable_literal_mappings.get_equality_literal(
                domain_id,
                ub + 1,
                &assignments_propositional,
                &assignments_integer,
            )
        );
    }

    #[test]
    fn check_correspondence_predicates_creating_new_int_domain() {
        let mut variable_literal_mappings = VariableLiteralMappings::default();
        let mut assignments_integer = AssignmentsInteger::default();
        let mut watch_list_cp = WatchListCP::default();
        let mut watch_list_propositional = WatchListPropositional::default();
        let mut clausal_propagator = ClausalPropagator::default();
        let mut assignments_propositional = AssignmentsPropositional::default();
        let mut clausal_allocator = ClauseAllocator::default();

        let lower_bound = 0;
        let upper_bound = 10;
        let domain_id = variable_literal_mappings.create_new_domain(
            lower_bound,
            upper_bound,
            &mut assignments_integer,
            &mut watch_list_cp,
            &mut watch_list_propositional,
            &mut clausal_propagator,
            &mut assignments_propositional,
            &mut clausal_allocator,
        );

        for bound in lower_bound + 1..upper_bound {
            let lower_bound_predicate = predicate![domain_id >= bound];
            let equality_predicate = predicate![domain_id == bound];
            for predicate in [lower_bound_predicate, equality_predicate] {
                let literal = variable_literal_mappings.get_literal(
                    predicate.try_into().unwrap(),
                    &assignments_propositional,
                    &assignments_integer,
                );
                assert!(variable_literal_mappings.literal_to_predicates[literal]
                    .contains(&predicate.try_into().unwrap()))
            }
        }
    }
}
