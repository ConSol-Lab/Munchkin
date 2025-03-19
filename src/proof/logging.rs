use std::fs::File;
use std::io::Write;
use std::num::NonZero;
use std::path::PathBuf;

use drcp_format::steps::StepId;
use drcp_format::writer::LiteralCodeProvider;
use drcp_format::writer::ProofWriter;
use drcp_format::AtomicConstraint;
use drcp_format::Comparison;
use drcp_format::IntAtomicConstraint;
use drcp_format::LiteralDefinitions;

use crate::basic_types::KeyedVec;
use crate::engine::cp::AssignmentsInteger;
use crate::engine::cp::VariableLiteralMappings;
use crate::engine::sat::AssignmentsPropositional;
use crate::engine::VariableNames;
use crate::predicates::IntegerPredicate;
use crate::variables::Literal;
use crate::variables::PropositionalVariable;

/// Logs a proof to a file.
#[derive(Default, Debug)]
pub struct Proof {
    /// The proof, if one is being logged.
    proof_impl: Option<ProofImpl>,
}

/// A dummy step ID that is returned if no proof is being logged.
const DUMMY_STEP_ID: StepId = NonZero::new(1).unwrap();

impl Proof {
    pub(crate) fn new(proof: File, lits: PathBuf) -> Self {
        Proof {
            proof_impl: Some(ProofImpl {
                writer: ProofWriter::new(
                    drcp_format::Format::Text,
                    proof,
                    ProofLiterals::default(),
                ),
                lits,
                full_proof: false,
            }),
        }
    }

    /// Conclude the proof with the given bound on the objective variable.
    pub(crate) fn conclude_proof_optimal(
        &mut self,
        bound: Literal,
        variable_names: &VariableNames,
        variable_literal_mapping: &VariableLiteralMappings,
    ) {
        if let Some(proof) = self.proof_impl.take() {
            let _ = proof.optimal(bound, variable_names, variable_literal_mapping);
        }
    }

    /// Conclude the proof with the unsat conclusion.
    pub(crate) fn conclude_proof_unsat(
        &mut self,
        variable_names: &VariableNames,
        variable_literal_mapping: &VariableLiteralMappings,
    ) {
        if let Some(proof) = self.proof_impl.take() {
            let _ = proof.unsat(variable_names, variable_literal_mapping);
        }
    }

    /// Log a nogood to the proof. `literals` should be treated as the conjunction
    /// `/\literals -> false`.
    pub(crate) fn log_nogood(
        &mut self,
        literals: impl IntoIterator<Item = Literal>,
        hints: impl IntoIterator<Item = StepId>,
    ) -> std::io::Result<StepId> {
        if let Some(proof) = self.proof_impl.as_mut() {
            proof.log_nogood(literals, hints)
        } else {
            Ok(DUMMY_STEP_ID)
        }
    }
}

/// The actual implementation of the proof log.
#[derive(Debug)]
struct ProofImpl {
    writer: ProofWriter<File, ProofLiterals>,
    /// Path to the literal mapping file.
    lits: PathBuf,
    /// True when we are logging the full proof, with inferences and hints.
    full_proof: bool,
}

impl ProofImpl {
    /// Log a nogood to the proof. `literals` should be treated as the conjunction
    /// `/\literals -> false`.
    pub(crate) fn log_nogood(
        &mut self,
        literals: impl IntoIterator<Item = Literal>,
        hints: impl IntoIterator<Item = StepId>,
    ) -> std::io::Result<StepId> {
        let hints = if self.full_proof { Some(hints) } else { None };

        self.writer.log_nogood(literals, hints)
    }

    pub(crate) fn unsat(
        self,
        variable_names: &VariableNames,
        variable_literal_mapping: &VariableLiteralMappings,
    ) -> std::io::Result<()> {
        let literals = self.writer.unsat()?;
        let file = File::create(self.lits)?;
        literals.write(file, variable_names, variable_literal_mapping)
    }

    pub(crate) fn optimal(
        self,
        objective_bound: Literal,
        variable_names: &VariableNames,
        variable_literal_mapping: &VariableLiteralMappings,
    ) -> std::io::Result<()> {
        let literals = self.writer.optimal(objective_bound)?;
        let file = File::create(self.lits)?;
        literals.write(file, variable_names, variable_literal_mapping)
    }
}

#[derive(Debug)]
pub(crate) struct ProofLiterals {
    /// All the variables seen in the proof log.
    variables: KeyedVec<PropositionalVariable, Option<NonZero<u32>>>,
    /// The next code that can be used when a new variable is encountered.
    next_code: NonZero<u32>,
}

impl Default for ProofLiterals {
    fn default() -> Self {
        ProofLiterals {
            variables: KeyedVec::default(),
            next_code: NonZero::new(1).unwrap(),
        }
    }
}

impl ProofLiterals {
    /// Create a new [`ProofLiterals`] instance.
    pub(crate) fn new(
        definitions: LiteralDefinitions<String>,
        assignments_integer: &AssignmentsInteger,
        assignments_propositional: &AssignmentsPropositional,
        variable_names: &VariableNames,
        variable_literal_mapping: &VariableLiteralMappings,
    ) -> Self {
        let mut variables = KeyedVec::default();
        let next_code = definitions
            .iter()
            .map(|(id, _)| id)
            .max()
            .unwrap_or(NonZero::new(1).unwrap());

        for (code, definitions) in definitions.iter() {
            // A bit of a hack, but we assume the literal mapping is from Munchkin. This means
            // equivalent literals will also be equivalent to what is generated in the current
            // variable_literal_mapping.

            if definitions.is_empty() {
                continue;
            }

            let representative = &definitions[0];
            let integer_predicate = atomic_to_integer_predicate(representative, variable_names);
            let literal = variable_literal_mapping.get_literal(
                integer_predicate,
                assignments_propositional,
                assignments_integer,
            );

            assert!(literal.is_positive());

            variables.insert_with_default(literal.get_propositional_variable(), Some(code), None);
        }

        ProofLiterals {
            variables,
            next_code,
        }
    }

    pub(crate) fn write(
        self,
        sink: impl Write,
        variable_names: &VariableNames,
        variable_literal_mapping: &VariableLiteralMappings,
    ) -> std::io::Result<()> {
        let entries = self
            .variables
            .into_entries()
            .filter_map(|(variable, code)| code.map(|c| (variable, c)));

        let mut definitions = LiteralDefinitions::default();

        for (variable, code) in entries {
            let predicates =
                variable_literal_mapping.get_predicates_for_literal(Literal::new(variable, true));

            let atomics =
                predicates.map(|predicate| integer_predicate_to_atomic(predicate, variable_names));

            for atomic in atomics {
                definitions.add(code, atomic);
            }
        }

        definitions.write(sink)
    }

    fn get_next_code(&mut self) -> NonZero<u32> {
        let code = self.next_code;
        self.next_code = self
            .next_code
            .checked_add(1)
            .expect("fewer than i32::MAX literals");
        code
    }
}

fn atomic_to_integer_predicate(
    atomic: &AtomicConstraint<String>,
    variable_names: &VariableNames,
) -> IntegerPredicate {
    let AtomicConstraint::Int(atomic) = atomic else {
        panic!("Only integers are supported.");
    };

    let domain_id = variable_names
        .get_domain_by_name(&atomic.name)
        .expect("variable with name exists");

    match atomic.comparison {
        Comparison::GreaterThanEqual => IntegerPredicate::LowerBound {
            domain_id,
            lower_bound: atomic.value as i32,
        },
        Comparison::LessThanEqual => IntegerPredicate::UpperBound {
            domain_id,
            upper_bound: atomic.value as i32,
        },
        Comparison::Equal => IntegerPredicate::Equal {
            domain_id,
            equality_constant: atomic.value as i32,
        },
        Comparison::NotEqual => IntegerPredicate::NotEqual {
            domain_id,
            not_equal_constant: atomic.value as i32,
        },
    }
}

fn integer_predicate_to_atomic(
    predicate: IntegerPredicate,
    variable_names: &VariableNames,
) -> AtomicConstraint<&str> {
    match predicate {
        IntegerPredicate::LowerBound {
            domain_id,
            lower_bound,
        } => AtomicConstraint::Int(IntAtomicConstraint {
            name: variable_names
                .get_int_name(domain_id)
                .expect("integer domain is unnamed"),
            comparison: Comparison::GreaterThanEqual,
            value: lower_bound.into(),
        }),
        IntegerPredicate::UpperBound {
            domain_id,
            upper_bound,
        } => AtomicConstraint::Int(IntAtomicConstraint {
            name: variable_names
                .get_int_name(domain_id)
                .expect("integer domain is unnamed"),
            comparison: Comparison::LessThanEqual,
            value: upper_bound.into(),
        }),
        IntegerPredicate::NotEqual {
            domain_id,
            not_equal_constant,
        } => AtomicConstraint::Int(IntAtomicConstraint {
            name: variable_names
                .get_int_name(domain_id)
                .expect("integer domain is unnamed"),
            comparison: Comparison::NotEqual,
            value: not_equal_constant.into(),
        }),
        IntegerPredicate::Equal {
            domain_id,
            equality_constant,
        } => AtomicConstraint::Int(IntAtomicConstraint {
            name: variable_names
                .get_int_name(domain_id)
                .expect("integer domain is unnamed"),
            comparison: Comparison::Equal,
            value: equality_constant.into(),
        }),
    }
}

impl LiteralCodeProvider for ProofLiterals {
    type Literal = Literal;

    fn to_code(&mut self, literal: Self::Literal) -> NonZero<i32> {
        let variable = literal.get_propositional_variable();

        self.variables.accomodate(variable, None);

        let variable_code = if let Some(code) = self.variables[variable] {
            code
        } else {
            let code = self.get_next_code();
            self.variables[variable] = Some(code);

            code
        };

        let code: NonZero<i32> = variable_code
            .try_into()
            .expect("fewer than i32::MAX literals");

        if literal.is_positive() {
            code
        } else {
            -code
        }
    }
}
