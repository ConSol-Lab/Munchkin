mod sequential_sum;
mod totalizer;

use std::num::NonZero;

pub(crate) use sequential_sum::SequentialSum;
pub(crate) use totalizer::Totalizer;

use crate::constraints::Constraint;
use crate::model::LinearEncoding;
use crate::predicate;
use crate::predicates::Predicate;
use crate::variables::DomainId;
use crate::variables::IntegerVariable;
use crate::ConstraintOperationError;
use crate::Solver;

pub fn less_than_or_equals<Var: IntegerVariable + 'static>(
    terms: impl Into<Box<[Var]>>,
    rhs: i32,
    encoding: LinearEncoding,
) -> impl Constraint {
    EncodedLinearLeq {
        encoder: create_encoder(encoding),
        terms: terms.into(),
        predicate: move |domain_id: DomainId| predicate![domain_id <= rhs],
    }
}

pub fn equals<Var: IntegerVariable + 'static>(
    terms: impl Into<Box<[Var]>>,
    rhs: i32,
    encoding: LinearEncoding,
) -> impl Constraint {
    EncodedLinearLeq {
        encoder: create_encoder(encoding),
        terms: terms.into(),
        predicate: move |domain_id: DomainId| predicate![domain_id == rhs],
    }
}

fn create_encoder<Var: IntegerVariable>(
    encoding: LinearEncoding,
) -> Box<dyn LinearSumEncoder<Var>> {
    match encoding {
        LinearEncoding::Totalizer => Box::new(Totalizer),
        LinearEncoding::SequentialSums => Box::new(SequentialSum),
    }
}

struct EncodedLinearLeq<Var, Fn> {
    encoder: Box<dyn LinearSumEncoder<Var>>,
    terms: Box<[Var]>,
    predicate: Fn,
}

impl<Var, Fn> Constraint for EncodedLinearLeq<Var, Fn>
where
    Var: IntegerVariable,
    Fn: FnOnce(DomainId) -> Predicate,
{
    fn post(self, solver: &mut Solver, _: NonZero<u32>) -> Result<(), ConstraintOperationError> {
        let domain_id = self.encoder.encode(solver, &self.terms);
        let literal = solver.get_literal((self.predicate)(domain_id));
        solver.add_clause([literal])?;

        Ok(())
    }

    fn implied_by(
        self,
        _: &mut Solver,
        _: crate::variables::Literal,
        _: NonZero<u32>,
    ) -> Result<(), ConstraintOperationError> {
        unreachable!("reification of encoded linear is not supported")
    }
}

/// A common trait for all linear sum encoders.
pub(crate) trait LinearSumEncoder<Var> {
    /// Encode a linear sum `\sum x_i` and return the integer variable `y = \sum x_i` representing
    /// the evaluation of the sum.
    fn encode(&self, solver: &mut Solver, terms: &[Var]) -> DomainId;
}
