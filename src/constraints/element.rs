use std::num::NonZero;

use super::Constraint;
use crate::constraints;
use crate::predicate;
use crate::propagators::element::ElementPropagator;
use crate::variables::IntegerVariable;
use crate::variables::Literal;
use crate::ConstraintOperationError;
use crate::Solver;

/// Creates the [element](https://sofdem.github.io/gccat/gccat/Celement.html) [`Constraint`] which states that `array[index] = rhs`.
pub fn element<ElementVar: IntegerVariable + 'static>(
    index: impl IntegerVariable + 'static,
    array: impl Into<Box<[ElementVar]>>,
    rhs: impl IntegerVariable + 'static,
) -> impl Constraint {
    ElementPropagator::new(index, array.into(), rhs)
}

pub fn element_decomposition<ElementVar: IntegerVariable + 'static>(
    index: impl IntegerVariable + 'static,
    array: impl Into<Box<[ElementVar]>>,
    rhs: ElementVar,
) -> impl Constraint {
    ElementDecomposition {
        index,
        array: array.into(),
        rhs,
    }
}

struct ElementDecomposition<Index, ArrayVar> {
    index: Index,
    array: Box<[ArrayVar]>,
    rhs: ArrayVar,
}

impl<Index, ArrayVar> Constraint for ElementDecomposition<Index, ArrayVar>
where
    Index: IntegerVariable,
    ArrayVar: IntegerVariable + 'static,
{
    fn post(self, solver: &mut Solver, tag: NonZero<u32>) -> Result<(), ConstraintOperationError> {
        // Index is 1-indexed, but the implementation is 0-indexed.
        let index = self.index.offset(-1);

        for (i, array_element) in self.array.iter().enumerate() {
            let idx_eq_i = solver.get_literal(predicate![index == i as i32]);

            solver
                .add_constraint(constraints::binary_equals(
                    array_element.clone(),
                    self.rhs.clone(),
                ))
                .implied_by(idx_eq_i, tag)?;
        }

        Ok(())
    }

    fn implied_by(
        self,
        _: &mut Solver,
        _: Literal,
        _: NonZero<u32>,
    ) -> Result<(), ConstraintOperationError> {
        todo!("half-reification of element encoding")
    }
}
