use std::any::Any;
use std::fs::File;
use std::path::PathBuf;
use std::time::Duration;

use anyhow::Context;
use clap::ValueEnum;
use drcp_format::reader::ProofReader;
use drcp_format::LiteralDefinitions;

use self::termination::TerminationCondition;
use crate::branching::Brancher;
use crate::engine::constraint_satisfaction_solver::ConflictResolutionStrategy;
use crate::engine::constraint_satisfaction_solver::NogoodMinimisationStrategy;
use crate::engine::termination;
use crate::model::Globals;
use crate::model::IntVariable;
use crate::model::LinearEncoding;
use crate::model::Model;
use crate::model::Output;
use crate::model::VariableMap;
use crate::optimisation::linear_sat_unsat::LinearSatUnsat;
use crate::optimisation::CoreGuidedSearch;
use crate::optimisation::LinearUnsatSat;
use crate::optimisation::OptimisationStrategy;
use crate::options::SolverOptions;
use crate::predicate;
use crate::proof::checking::verify_proof;
use crate::proof::processing::process_proof;
use crate::proof::processing::Processor;
use crate::proof::Proof;
use crate::results::OptimisationResult;
use crate::results::ProblemSolution;
use crate::results::SolutionReference;
use crate::solver::OptimisationDirection::Minimise;
use crate::statistics::configure;
use crate::termination::TimeBudget;
use crate::Solver;

pub trait OptionEnum: ValueEnum + Clone + Send + Sync + Any + Default {}
impl<T> OptionEnum for T where T: ValueEnum + Clone + Send + Sync + Any + Default {}

#[derive(Debug, clap::Parser)]
pub struct Cli<SearchStrategies: OptionEnum> {
    /// The data for the model.
    pub instance: PathBuf,

    #[command(subcommand)]
    pub command: Action<SearchStrategies>,
}

#[derive(Clone, Debug, clap::Subcommand)]
pub enum Action<SearchStrategies: OptionEnum> {
    /// Solve the given instance.
    Solve {
        /// The constraints that should _not_ be decomposed.
        ///
        /// Multiple constraints can be provided by passing this option multiple times.
        #[arg(short = 'G', long = "global")]
        globals: Vec<Globals>,

        /// The encoding to use for the linear constraint. If none is supplied, the propagator is
        /// used.
        #[arg(long)]
        linear_encoding: Option<LinearEncoding>,

        /// The file path to which the proof will be written.
        ///
        /// If no path is provided, a proof will not be produced.
        #[arg(short = 'P')]
        proof_path: Option<PathBuf>,

        /// The search strategy to use.
        #[arg(short = 'S', long = "search", value_enum, default_value_t)]
        search_strategy: SearchStrategies,

        #[arg(short = 'M', long = "minimisation", default_value_t)]
        minimisation: NogoodMinimisationStrategy,

        /// The conflict resolution strategy to use
        #[arg(short = 'C', long = "resolution", default_value_t)]
        conflict_resolution: ConflictResolutionStrategy,

        /// Whether to use a non-trivial conflict explanation
        #[arg(short = 'E', long = "non-trivial-conflict")]
        use_non_trivial_conflict_explanation: bool,

        /// Whether to use a non-trivial propagation explanation
        #[arg(short = 'R', long = "non-trivial-propagation")]
        use_non_trivial_propagation_explanation: bool,
        /// The optimisation strategy which is used by the solver
        #[arg(short = 'O', long = "optimisation", default_value_t)]
        optimisation_strategy: OptimisationStrategy,

        /// The number of seconds the solver is allowed to run.
        time_out: u64,
    },

    Processing {
        /// The path to the proof scaffold.
        scaffold: PathBuf,

        /// Output path of the full proof. The new literal mapping will be in the same location but
        /// with the extension `.lits`.
        output_path: PathBuf,
    },

    /// Check the proof of this instance.
    Verify {
        /// The file path to the proof.
        proof_path: PathBuf,
    },
}

/// Definition of a problem instance to be solved with Munchkin.
pub trait Problem<SearchStrategies>: Sized {
    /// Constructor function which creates an instance of `Self`, as well as the [`Model`] for the
    /// problem.
    fn create(data: dzn_rs::DataFile<i32>) -> anyhow::Result<(Self, Model)>;

    /// The objective variable.
    fn objective(&self) -> IntVariable;

    fn get_search(
        &self,
        strategy: SearchStrategies,
        solver: &Solver,
        solver_variables: &VariableMap,
    ) -> impl Brancher + 'static;

    fn get_output_variables(&self) -> impl Iterator<Item = Output> + '_;
}

#[macro_export]
macro_rules! entry_point {
    (problem = $problem:ident, search_strategies = $search_strategies:ident) => {
        fn main() -> anyhow::Result<()> {
            $crate::runner::run::<$problem, $search_strategies>()
        }
    };
}

pub fn run<ProblemType, SearchStrategies>() -> anyhow::Result<()>
where
    ProblemType: Problem<SearchStrategies>,
    SearchStrategies: OptionEnum,
{
    use anyhow::Context;
    use clap::Parser;

    let args = Cli::<SearchStrategies>::parse();

    configure(true, "%% ", None);

    let data = std::fs::read_to_string(&args.instance)
        .with_context(|| format!("Error reading {}", args.instance.display()))?;

    let data = dzn_rs::parse::<i32>(data.as_bytes())
        .with_context(|| format!("Failed to parse DZN from {}", args.instance.display()))?;

    let (instance, model) = ProblemType::create(data)?;

    match args.command {
        Action::Solve {
            globals,
            linear_encoding,
            proof_path,
            search_strategy,
            conflict_resolution,
            minimisation,
            optimisation_strategy,
            time_out,
            use_non_trivial_conflict_explanation: use_non_generic_conflict_explanation,
            use_non_trivial_propagation_explanation: use_non_generic_propagation_explanation,
        } => solve(
            model,
            instance,
            search_strategy,
            optimisation_strategy,
            globals,
            linear_encoding,
            conflict_resolution,
            minimisation,
            use_non_generic_conflict_explanation,
            use_non_generic_propagation_explanation,
            proof_path,
            Duration::from_secs(time_out),
        ),
        Action::Processing {
            scaffold,
            output_path,
        } => process(model, scaffold, output_path),
        Action::Verify { proof_path } => verify(model, proof_path),
    }
}

#[allow(clippy::too_many_arguments, reason = "All arguments need to be passed")]
pub fn solve<SearchStrategies>(
    model: Model,
    instance: impl Problem<SearchStrategies>,
    search_strategy: SearchStrategies,
    optimisation_strategy: OptimisationStrategy,
    globals: Vec<Globals>,
    linear_encoding: Option<LinearEncoding>,
    conflict_resolution: ConflictResolutionStrategy,
    minimisation: NogoodMinimisationStrategy,
    use_non_generic_conflict_explanation: bool,
    use_non_generic_propagation_explanation: bool,
    proof_path: Option<PathBuf>,
    time_out: Duration,
) -> anyhow::Result<()> {
    let mut time_budget = TimeBudget::starting_now(time_out);
    let proof = proof_path
        .map(|path| {
            let proof_file = File::create(&path)
                .with_context(|| format!("Failed to create proof file {}", path.display()))?;

            Ok::<_, anyhow::Error>(Proof::new(proof_file, path.with_extension("lits")))
        })
        .transpose()?;

    let (mut solver, solver_variables) = model.into_solver(
        SolverOptions {
            conflict_resolver: conflict_resolution,
            minimisation_strategy: minimisation,
            use_non_generic_conflict_explanation,
            use_non_generic_propagation_explanation,
            proof: proof.unwrap_or_default(),
            ..Default::default()
        },
        |global| globals.contains(&global),
        linear_encoding,
        &mut time_budget,
    );

    if time_budget.should_stop() {
        solver.log_statistics();
        println!("UNKNOWN");
        return Ok(());
    }

    let output_variables: Vec<_> = instance.get_output_variables().collect();
    let callback_solver_variables = solver_variables.clone();

    let solution_callback = move |solver: &Solver, solution: SolutionReference| {
        solver.log_statistics();
        for output in &output_variables {
            print_output(output, &callback_solver_variables, &solution);
        }

        println!("----------");
    };

    let mut brancher = instance.get_search(search_strategy, &solver, &solver_variables);
    let objective_variable = solver_variables.to_solver_variable(instance.objective());

    let result = match optimisation_strategy {
        OptimisationStrategy::LinearSatUnsat => solver.optimise(
            &mut brancher,
            &mut time_budget,
            LinearSatUnsat::new(Minimise, objective_variable.clone(), solution_callback),
        ),
        OptimisationStrategy::LinearUnsatSat => solver.optimise(
            &mut brancher,
            &mut time_budget,
            LinearUnsatSat::new(Minimise, objective_variable.clone(), solution_callback),
        ),
        OptimisationStrategy::CoreGuided => solver.optimise(
            &mut brancher,
            &mut time_budget,
            CoreGuidedSearch::new(
                Minimise,
                vec![objective_variable.clone()],
                solution_callback,
            ),
        ),
        OptimisationStrategy::LBBD => todo!(),
    };

    match result {
        // Printing of the solution is handled in the callback.
        OptimisationResult::Optimal(solution) => {
            let objective_bound = solution.get_integer_value(objective_variable.clone());
            let literal = solver.get_literal(predicate![objective_variable >= objective_bound]);
            solver.conclude_proof_optimal(literal);

            println!("==========");
            solver.log_statistics()
        }
        OptimisationResult::Satisfiable(_) => {}

        OptimisationResult::Unsatisfiable => {
            solver.log_statistics();
            solver.conclude_proof_unsat();
            println!("UNSATISFIABLE");
        }
        OptimisationResult::Unknown => {
            solver.log_statistics();
            println!("UNKNOWN");
        }
    }

    Ok(())
}

fn print_output(output: &Output, solver_variables: &VariableMap, solution: &SolutionReference) {
    let name = solver_variables.get_name(output);

    match output {
        Output::Variable(variable) => {
            let solver_variable = solver_variables.to_solver_variable(*variable);

            println!(
                "{name} = {};",
                solution.get_integer_value(solver_variable.clone())
            );
        }

        Output::Array(int_variable_array) => {
            let solver_variables = solver_variables.get_array(*int_variable_array);
            let num_variables = solver_variables.len();

            print!("{name} = [");
            for (idx, variable) in solver_variables.into_iter().enumerate() {
                print!("{}", solution.get_integer_value(variable));

                if idx < num_variables - 1 {
                    print!(", ");
                }
            }
            println!("];");
        }
        Output::TwoDimensionalArray(matrix) => {
            println!("{name} =");
            print!("[| ");
            for (index, for_i) in solver_variables.get_matrix(*matrix).into_iter().enumerate() {
                if index == 0 {
                } else {
                    print!(" | ");
                }
                for (var_index, variable) in for_i.iter().enumerate() {
                    let value = solution.get_integer_value(variable.clone());

                    if value == 0 {
                        print!("false");
                    } else if value == 1 {
                        print!("true");
                    } else {
                        panic!("For now we have just implemented this for 2D boolean arrays")
                    }
                    if var_index < for_i.len() - 1 {
                        print!(", ");
                    }
                }
                println!("");
            }
            println!("|];");
        }
    }
}

pub fn verify(model: Model, proof_path: PathBuf) -> anyhow::Result<()> {
    // First, we read the contents of the `.drcp` and `.lits` files.
    let lits_file = proof_path.with_extension("lits");
    let lits = File::open(&lits_file)
        .with_context(|| format!("Failed to open {}", lits_file.display()))?;
    let proof_file = File::open(&proof_path)
        .with_context(|| format!("Failed to open {}", proof_path.display()))?;

    // Then, we parse the literal definitions from the `.lits` file.
    let literals = LiteralDefinitions::<String>::parse(lits).with_context(|| {
        format!(
            "Failed to parse literal definition from {}",
            lits_file.display()
        )
    })?;

    // Using the literal defintions, we can parse the proof steps from the `.drcp` file.
    let proof = ProofReader::new(proof_file, literals);

    // Finally, we can run the checker, giving it the proof reader and the model.
    verify_proof(model, proof)
}

fn process(model: Model, scaffold: PathBuf, output: PathBuf) -> anyhow::Result<()> {
    // First, we create a processor from the model.
    let processor = Processor::from(model);

    // Then, we read the contents of the `.drcp` and `.lits` files.
    let lits_file = scaffold.with_extension("lits");
    let lits = File::open(&lits_file)
        .with_context(|| format!("Failed to open {}", lits_file.display()))?;
    let proof_file =
        File::open(&scaffold).with_context(|| format!("Failed to open {}", scaffold.display()))?;

    // Then, we parse the literal definitions from the `.lits` file.
    let definitions = LiteralDefinitions::<String>::parse(lits).with_context(|| {
        format!(
            "Failed to parse literal definition from {}",
            lits_file.display()
        )
    })?;

    // Using the literal defintions, we can parse the proof steps from the `.drcp` file.
    let proof = ProofReader::new(proof_file, processor.initialise_proof_literals(definitions));

    // Then, we can run the processor giving it the model, the proof reader and the output path.
    process_proof(processor, proof, output)
}
