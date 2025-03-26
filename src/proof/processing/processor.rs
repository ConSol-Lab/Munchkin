use std::fs::File;
use std::num::NonZero;

use drcp_format::steps::Nogood;
use drcp_format::steps::StepId;

use super::rp_engine::ConflictReason;
use super::rp_engine::RpClauseHandle;
use super::rp_engine::RpEngine;
use crate::basic_types::HashMap;
use crate::model::Model;
use crate::options::SolverOptions;
use crate::proof::ProofLiterals;
use crate::termination::Indefinite;
use crate::variables::Literal;

pub(crate) struct Processor {
    engine: RpEngine,
    handles: HashMap<RpClauseHandle, StepId>,
    bound: Option<Literal>,
}

impl From<Model> for Processor {
    fn from(model: Model) -> Self {
        let (solver, _) = model.into_solver(
            SolverOptions::default(),
            |globals| match globals {
                crate::model::Globals::DfsCircuit
                | crate::model::Globals::EnergeticReasoningCumulative => false,
                crate::model::Globals::Element
                | crate::model::Globals::AllDifferent
                | crate::model::Globals::Cumulative
                | crate::model::Globals::Maximum
                | crate::model::Globals::ForwardCheckingCircuit
                | crate::model::Globals::TimeTableCumulative => true,
            },
            None,
            &mut Indefinite,
        );

        Processor {
            engine: RpEngine::new(solver),
            handles: HashMap::default(),
            bound: None,
        }
    }
}

#[allow(dead_code, reason = "will be used in assignment")]
impl Processor {
    /// Sets up the processor to take the objective into account.
    pub(crate) fn set_objective_bound(&mut self, bound: Literal) {
        self.bound = Some(!bound);
    }

    /// Adds a nogood to the propagation engine. This nogood will be used in
    /// [`Processor::propagate_under_assumptions`]. It can be removed through
    /// [`Processor::remove_nogood`].
    ///
    /// If adding this nogood causes the state to be unsatisfiable under propagation, the processor
    /// is now in an inconsistent state. To make use of the processor after that, remove this
    /// nogood.
    pub(crate) fn add_removable_nogood(
        &mut self,
        nogood: Nogood<Vec<Literal>, Vec<StepId>>,
    ) -> Result<(), ProcessorConflict> {
        let handle = self
            .engine
            .add_rp_clause(nogood.literals.into_iter().map(|lit| !lit))
            .map_err(|(handle, reasons)| {
                let _ = self.handles.insert(handle, nogood.id);
                self.map_reasons(reasons)
            })?;

        let _ = self.handles.insert(handle, nogood.id);

        self.propagate_under_assumptions(self.bound)?;

        Ok(())
    }

    /// Remove the most recently added nogood that was added with
    /// [`Processor::add_removable_nogood()`]. If no such nogood exists, return `None`.
    pub(crate) fn remove_top_nogood(&mut self) -> Option<Vec<Literal>> {
        self.engine
            .remove_last_rp_clause()
            .map(|clause| clause.into_iter().map(|lit| !lit).collect())
    }

    /// Propagate all the constraints to fixpoint.
    pub(crate) fn propagate_under_assumptions(
        &mut self,
        assumptions: impl IntoIterator<Item = Literal>,
    ) -> Result<(), ProcessorConflict> {
        self.engine
            .propagate_under_assumptions(self.bound.iter().copied().chain(assumptions))
            .map_err(|reasons| self.map_reasons(reasons))
    }

    /// Creates a new instance of [`ProofLiterals`] linked to the state in the processor.
    pub(crate) fn initialise_proof_literals(
        &self,
        definitions: drcp_format::LiteralDefinitions<String>,
    ) -> ProofLiterals {
        ProofLiterals::new(
            definitions,
            &self.engine.solver.assignments_integer,
            &self.engine.solver.assignments_propositional,
            &self.engine.solver.variable_names,
            &self.engine.solver.variable_literal_mappings,
        )
    }

    /// Writes the literal mapping to the given file.
    pub(crate) fn write_proof_literals(
        &self,
        literals: ProofLiterals,
        file: File,
    ) -> anyhow::Result<()> {
        literals.write(
            file,
            &self.engine.solver.variable_names,
            &self.engine.solver.variable_literal_mappings,
        )?;
        Ok(())
    }

    fn map_reasons(&self, reasons: Vec<ConflictReason>) -> ProcessorConflict {
        let propagations = reasons
            .into_iter()
            .map(|reason| match reason {
                ConflictReason::Clause(handle) => {
                    Propagation::Nogood(self.handles.get(&handle).copied().unwrap())
                }
                ConflictReason::Propagator {
                    premises,
                    propagated,
                    label,
                    tag,
                } => Propagation::Propagator {
                    tag,
                    label,
                    premises,
                    propagated,
                },
            })
            .collect();
        ProcessorConflict(propagations)
    }
}

#[derive(Clone, Debug)]
pub(crate) struct ProcessorConflict(Vec<Propagation>);

impl IntoIterator for ProcessorConflict {
    type Item = Propagation;

    type IntoIter = std::vec::IntoIter<Propagation>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl ProcessorConflict {
    /// Iterate over the reasons for this conflict.
    #[allow(dead_code, reason = "may be used in assignment")]
    pub(crate) fn iter(&self) -> impl Iterator<Item = Propagation> + '_ {
        self.0.iter().cloned()
    }
}

/// An edge in the implication graph. It is either a propagator or a nogood.
#[derive(Debug, Clone)]
#[allow(dead_code, reason = "may be used in assignment")]
pub(crate) enum Propagation {
    Nogood(StepId),
    Propagator {
        tag: NonZero<u32>,
        label: &'static str,
        premises: Vec<Literal>,
        propagated: Option<Literal>,
    },
}
