#![allow(unused, reason = "this file is a skeleton for the assignment")]

use crate::basic_types::PropagationStatusCP;
use crate::conjunction;
use crate::engine::cp::domain_events::DomainEvents;
use crate::engine::cp::propagation::PropagationContextMut;
use crate::engine::cp::propagation::Propagator;
use crate::engine::cp::propagation::PropagatorInitialisationContext;
use crate::engine::cp::propagation::ReadDomains;
use crate::predicates::PropositionalConjunction;
use crate::variables::IntegerVariable;

pub(crate) struct AllDifferentPropagator<Var> {
    variables: Box<[Var]>, // TODO: you can add more fields here!
}

impl<Var> AllDifferentPropagator<Var> {
    pub(crate) fn new(variables: Box<[Var]>) -> Self {
        Self { variables }
    }
}

impl<Var: IntegerVariable + 'static> Propagator for AllDifferentPropagator<Var> {
    fn name(&self) -> &str {
        "AllDifferent"
    }

    fn propagate(&self, mut context: PropagationContextMut) -> PropagationStatusCP {
        todo!()
    }

    fn initialise_at_root(
        &mut self,
        context: &mut PropagatorInitialisationContext,
    ) -> Result<(), PropositionalConjunction> {
        todo!()
    }
}
