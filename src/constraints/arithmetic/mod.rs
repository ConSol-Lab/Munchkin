mod equality;
mod inequality;

use std::num::NonZero;

pub use equality::*;
pub use inequality::*;

use super::Constraint;
use crate::propagators::arithmetic::maximum::MaximumPropagator;
use crate::variables::IntegerVariable;
use crate::variables::Literal;
use crate::ConstraintOperationError;
use crate::Solver;

/// Creates the [`Constraint`] `a + b = c`.
pub fn plus<Var: IntegerVariable + 'static>(a: Var, b: Var, c: Var) -> impl Constraint {
    equals([a.scaled(1), b.scaled(1), c.scaled(-1)], 0)
}

/// Creates the [`Constraint`] `max(array) = m`.
pub fn maximum<Var: IntegerVariable + 'static>(
    array: impl Into<Box<[Var]>>,
    rhs: impl IntegerVariable + 'static,
) -> impl Constraint {
    MaximumPropagator::new(array.into(), rhs)
}

/// Creates the [`Constraint`] `max(array) = m`.
pub fn maximum_decomposition<Var: IntegerVariable + 'static>(
    array: impl Into<Box<[Var]>>,
    rhs: Var,
) -> impl Constraint {
    MaximumDecomposition {
        array: array.into(),
        rhs,
    }
}

struct MaximumDecomposition<Var> {
    array: Box<[Var]>,
    rhs: Var,
}

impl<Var> Constraint for MaximumDecomposition<Var>
where
    Var: IntegerVariable + 'static,
{
    fn post(self, solver: &mut Solver, tag: NonZero<u32>) -> Result<(), ConstraintOperationError> {
        for element in self.array {
            solver
                .add_constraint(binary_less_than_or_equals(element, self.rhs.clone()))
                .post(tag)?;
        }

        Ok(())
    }

    fn implied_by(
        self,
        _: &mut Solver,
        _: Literal,
        _: NonZero<u32>,
    ) -> Result<(), ConstraintOperationError> {
        todo!("implement half-reification for maximum decomposition")
    }
}
