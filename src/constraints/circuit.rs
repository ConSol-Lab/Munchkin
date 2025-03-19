use std::num::NonZero;

use super::Constraint;
use crate::constraints;
use crate::predicate;
use crate::propagators::circuit::DfsCircuitPropagator;
use crate::propagators::circuit::ForwardCheckingCircuitPropagator;
use crate::variables::AffineView;
use crate::variables::DomainId;
use crate::variables::Literal;
use crate::variables::TransformableVariable;
use crate::ConstraintOperationError;
use crate::Solver;

/// Creates a [`Constraint`] equivalent to [`circuit`], but using a decomposition rather than a
/// global propagator.
///
/// Note that the decomposition is exponential in the number of variables.
pub fn circuit(
    successor: impl Into<Box<[AffineView<DomainId>]>>,
    sub_circuit_elimination: SubCircuitElimination,
    use_all_different_decomposition: bool,
    use_element_decomposition: bool,
) -> impl Constraint {
    DecomposedCircuit {
        successors: successor.into(),
        sub_circuit_elimination,
        use_all_different_decomposition,
        use_element_decomposition,
    }
}

#[derive(Clone, Copy, Debug)]
pub enum SubCircuitElimination {
    Decomposition,
    ForwardChecking,
    Dfs,
}

struct DecomposedCircuit {
    successors: Box<[AffineView<DomainId>]>,
    sub_circuit_elimination: SubCircuitElimination,
    use_all_different_decomposition: bool,
    use_element_decomposition: bool,
}

impl Constraint for DecomposedCircuit {
    fn post(self, solver: &mut Solver, tag: NonZero<u32>) -> Result<(), ConstraintOperationError> {
        let DecomposedCircuit {
            successors,
            sub_circuit_elimination,
            use_all_different_decomposition,
            use_element_decomposition,
        } = self;

        match sub_circuit_elimination {
            SubCircuitElimination::Decomposition => post_sub_circuit_elimination_decomposition(
                solver,
                &successors,
                use_all_different_decomposition,
                use_element_decomposition,
                tag,
            )?,
            SubCircuitElimination::ForwardChecking => solver.add_propagator(
                ForwardCheckingCircuitPropagator::new(successors.clone()),
                tag,
            )?,
            SubCircuitElimination::Dfs => {
                solver.add_propagator(DfsCircuitPropagator::new(successors.clone()), tag)?
            }
        }

        if use_all_different_decomposition {
            solver
                .add_constraint(constraints::all_different_decomposition(successors.clone()))
                .post(tag)?;
        } else {
            solver
                .add_constraint(constraints::all_different(successors.clone()))
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
        todo!("implement half reification of decomposed circuit")
    }
}

fn post_sub_circuit_elimination_decomposition(
    solver: &mut Solver,
    successors: &[AffineView<DomainId>],
    use_all_different_decomposition: bool,
    use_element_decomposition: bool,
    tag: NonZero<u32>,
) -> Result<(), ConstraintOperationError> {
    let min = successors
        .iter()
        .map(|var| solver.lower_bound(var))
        .min()
        .unwrap();
    assert_eq!(1, min);

    let max = successors
        .iter()
        .map(|var| solver.upper_bound(var))
        .max()
        .unwrap();
    assert_eq!(i32::try_from(successors.len()).unwrap(), max);

    let order: Box<[_]> = (0..max)
        .map(|i| {
            let ub = if i == 0 { 1 } else { max };

            AffineView::from(solver.new_bounded_integer(1, ub))
        })
        .collect();

    for (i, successor) in successors.iter().enumerate() {
        let succ_order = solver.new_bounded_integer(1, max);

        if use_element_decomposition {
            solver
                .add_constraint(constraints::element_decomposition(
                    successor.clone(),
                    order.clone(),
                    succ_order.into(),
                ))
                .post(tag)?;
        } else {
            solver
                .add_constraint(constraints::element(
                    successor.clone(),
                    order.clone(),
                    succ_order,
                ))
                .post(tag)?;
        }

        let order_i_eq_max = solver.get_literal(predicate![order[i] == max]);

        solver
            .add_constraint(constraints::equals([succ_order], 1))
            .implied_by(order_i_eq_max, tag)?;
        solver
            .add_constraint(constraints::equals(
                [succ_order.into(), order[i].clone().scaled(-1)],
                1,
            ))
            .implied_by(!order_i_eq_max, tag)?;
    }

    if use_all_different_decomposition {
        solver
            .add_constraint(constraints::all_different_decomposition(order.clone()))
            .post(tag)?;
    } else {
        solver
            .add_constraint(constraints::all_different(order.clone()))
            .post(tag)?;
    }

    for (idx, var) in successors.iter().enumerate() {
        let idx: i32 = idx.try_into().unwrap();

        solver
            .add_constraint(constraints::not_equals([var.clone()], idx + 1))
            .post(tag)?;
    }

    Ok(())
}
