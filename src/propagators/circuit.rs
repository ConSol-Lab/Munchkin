use crate::{
    basic_types::PropagationStatusCP,
    engine::propagation::{PropagationContextMut, Propagator, PropagatorInitialisationContext},
    predicates::PropositionalConjunction,
    variables::IntegerVariable,
};

pub(crate) struct CircuitPropagator<Var> {
    successor: Box<[Var]>,
    // TODO: you can add more fields here!
}

impl<Var> CircuitPropagator<Var> {
    pub(crate) fn new(successor: Box<[Var]>) -> Self {
        Self { successor }
    }
}

impl<Var: IntegerVariable + 'static> Propagator for CircuitPropagator<Var> {
    fn name(&self) -> &str {
        "Circuit"
    }

    fn propagate(&self, _context: PropagationContextMut) -> PropagationStatusCP {
        todo!()
    }

    fn initialise_at_root(
        &mut self,
        _: &mut PropagatorInitialisationContext,
    ) -> Result<(), PropositionalConjunction> {
        todo!()
    }
}
