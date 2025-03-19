use std::fmt::Debug;
use std::num::NonZero;

use super::Constraint;
use crate::constraints;
use crate::propagators::cumulative::EnergeticReasoningPropagator;
use crate::propagators::cumulative::TimeTablePropagator;
use crate::variables::IntegerVariable;
use crate::variables::Literal;
use crate::ConstraintOperationError;
use crate::Solver;

#[derive(Clone, Copy, Debug)]
pub enum CumulativeImpl {
    TimeTable,
    EnergeticReasoning,
    Decomposition,
}

/// Creates the [Cumulative](https://sofdem.github.io/gccat/gccat/Ccumulative.html) [`Constraint`].
/// This constraint ensures that at no point in time, the cumulative resource usage of the tasks
/// exceeds `bound`.
pub fn cumulative<Var: IntegerVariable + 'static + Debug>(
    impl_strategy: CumulativeImpl,
    start_times: impl Into<Box<[Var]>>,
    durations: impl Into<Box<[u32]>>,
    resource_requirements: impl Into<Box<[u32]>>,
    resource_capacity: u32,
) -> impl Constraint {
    CumulativeConstraint {
        impl_strategy,
        start_times: start_times.into(),
        durations: durations.into(),
        resource_requirements: resource_requirements.into(),
        resource_capacity,
    }
}

struct CumulativeConstraint<Var> {
    impl_strategy: CumulativeImpl,
    start_times: Box<[Var]>,
    durations: Box<[u32]>,
    resource_requirements: Box<[u32]>,
    resource_capacity: u32,
}

impl<Var: IntegerVariable + 'static> Constraint for CumulativeConstraint<Var> {
    fn post(self, solver: &mut Solver, tag: NonZero<u32>) -> Result<(), ConstraintOperationError> {
        let CumulativeConstraint {
            impl_strategy,
            start_times,
            durations,
            resource_requirements,
            resource_capacity,
        } = self;

        match impl_strategy {
            CumulativeImpl::TimeTable => solver.add_propagator(
                TimeTablePropagator::new(
                    start_times,
                    durations,
                    resource_requirements,
                    resource_capacity,
                ),
                tag,
            ),
            CumulativeImpl::EnergeticReasoning => solver.add_propagator(
                EnergeticReasoningPropagator::new(
                    start_times,
                    durations,
                    resource_requirements,
                    resource_capacity,
                ),
                tag,
            ),
            CumulativeImpl::Decomposition => post_cumulative_decomposition(
                solver,
                &start_times,
                &durations,
                &resource_requirements,
                resource_capacity,
                tag,
            ),
        }
    }

    fn implied_by(
        self,
        _: &mut Solver,
        _: Literal,
        _: NonZero<u32>,
    ) -> Result<(), ConstraintOperationError> {
        todo!("implement cumulative decomposition with half-reification")
    }
}

fn post_cumulative_decomposition<Var: IntegerVariable + 'static>(
    solver: &mut Solver,
    start_times: &[Var],
    durations: &[u32],
    resource_requirements: &[u32],
    resource_capacity: u32,
    tag: NonZero<u32>,
) -> Result<(), ConstraintOperationError> {
    let horizon: u32 = durations.iter().sum();

    for timepoint in 0..=horizon {
        let mut usages = vec![];

        for task in 0..start_times.len() {
            let resource_requirement = resource_requirements[task] as i32;
            if resource_requirement == 0 {
                continue;
            }

            let is_active_at_timepoint = solver.new_literal();
            let usage_of_task_at_current_timepoint =
                solver.new_sparse_integer([0, resource_requirement]);

            // If the timepoint starts after or ends before `timepoint`, the resource usage
            // will be 0.
            solver
                .add_constraint(constraints::equals([usage_of_task_at_current_timepoint], 0))
                .reify(!is_active_at_timepoint, tag)?;

            let duration = durations[task];

            let ends_before = if duration > timepoint {
                solver.get_false_literal()
            } else {
                let literal = solver.new_literal();

                // ends_before <-> start[task] + duration[task] <= timepoint
                solver
                    .add_constraint(constraints::less_than_or_equals(
                        [start_times[task].clone()],
                        (timepoint - duration) as i32,
                    ))
                    .reify(literal, tag)?;

                literal
            };

            let starts_after = if timepoint + duration > horizon {
                solver.get_false_literal()
            } else {
                let literal = solver.new_literal();

                // starts_after <-> start[task] > timepoint
                // starts_after <-> start[task] >= timepoint + 1
                // starts_after <-> -start[task] <= -timepoint - 1
                solver
                    .add_constraint(constraints::less_than_or_equals(
                        [start_times[task].scaled(-1)],
                        -(timepoint as i32) - 1,
                    ))
                    .reify(literal, tag)?;

                literal
            };

            // !is_active_at_timepoint <-> (ends_before \/ starts_after)
            solver
                .add_constraint(constraints::clause([ends_before, starts_after]))
                .reify(!is_active_at_timepoint, tag)?;

            usages.push(usage_of_task_at_current_timepoint);
        }

        solver
            .add_constraint(constraints::less_than_or_equals(
                usages,
                resource_capacity as i32,
            ))
            .post(tag)?;
    }

    Ok(())
}
