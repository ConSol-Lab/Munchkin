use super::LinearSumEncoder;
use crate::variables::DomainId;
use crate::variables::IntegerVariable;
use crate::Solver;

pub(crate) struct Totalizer;

impl<Var: IntegerVariable> LinearSumEncoder<Var> for Totalizer {
    #[allow(unused_variables, reason = "will be used in assignment")]
    fn encode(&self, solver: &mut Solver, terms: &[Var]) -> DomainId {
        // Look at the trait definition to see what this function should return.
        todo!()
    }
}
