use super::ValueSelector;
use crate::branching::SelectionContext;
use crate::engine::predicates::predicate::Predicate;
use crate::engine::variables::IntegerVariable;
use crate::engine::variables::Literal;
use crate::engine::variables::PropositionalVariable;
use crate::predicate;

/// [`ValueSelector`] which chooses to assign the provided variable to its lowest-bound.
#[derive(Debug, Copy, Clone)]
pub struct InDomainMax;

impl<Var: IntegerVariable> ValueSelector<Var> for InDomainMax {
    fn select_value(
        &mut self,
        context: &mut SelectionContext,
        decision_variable: Var,
    ) -> Predicate {
        predicate!(decision_variable >= context.upper_bound(&decision_variable))
    }
}

impl ValueSelector<PropositionalVariable> for InDomainMax {
    fn select_value(
        &mut self,
        _context: &mut SelectionContext,
        decision_variable: PropositionalVariable,
    ) -> Predicate {
        Literal::new(decision_variable, true).into()
    }
}
