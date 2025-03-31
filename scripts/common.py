from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Iterable, Literal, List, Union
from subprocess import run
from enum import Enum
import shutil
import sys
import json

ModelType = Union[Literal["tsp"], Literal["rcpsp"]] 

DATA_DIR = (Path(__file__).parent / ".." / "data").resolve()
EXPERIMENT_DIR = (Path(__file__).parent / ".." / "experiments").resolve()

INSTANCES = {
    "tsp": (DATA_DIR / "tsp"),
    "rcpsp": (DATA_DIR / "rcpsp"),
}

MINIZINC_MODELS = {
    "tsp": (Path(__file__).parent / ".." / "models" / "tsp.mzn").resolve(),
    "rcpsp": (Path(__file__).parent / ".." / "models" / "rcpsp.mzn").resolve(),
}

SOLUTION_SEPARATOR = "-" * 10
OPTIMALITY_PROVEN = "=" * 10

class RunError(Enum):
    IncorrectSolution = 1,
    IncorrectOptimalSolution = 2,
    Both = 3,

class bcolors:
    OKGREEN = '\033[92m'
    FAIL = '\033[91m'
    ENDC = '\033[0m'


@dataclass
class Context:
    """The context for the current evaluation."""

    directory: Path
    """The path of the current evaluation runs."""

    runs: Path
    """The directory containing the log files."""

    model: ModelType
    """The model being evaluated."""

    timeout: int
    """The timeout to give to each instance."""

    commit_hash: str
    """The commit hash in the git history."""

    has_dirty_files: bool
    """True if the experiment is run with uncommitted changes."""

    executable: Path
    """The executable containing the model."""

    flags: List[str]
    """Flags provided to the model for every run. These typically set options in the solver."""

    with_proofs: bool
    """If true, enables scaffold logging."""
    

    def to_dict(self) -> dict:
        """Turn the context into a JSON-serializable dictionary."""

        return {
            "directory": str(self.directory),
            "runs": str(self.runs),
            "model": self.model,
            "timeout": self.timeout,
            "commit_hash": self.commit_hash,
            "has_dirty_files": self.has_dirty_files,
            "executable": str(self.executable),
            "flags": self.flags,
            "with_proofs": self.with_proofs,
        }


    @classmethod
    def from_dict(cls, dictionary: dict) -> 'Context':
        """Create a Context from a JSON-dictionary."""

        return cls(
            directory=Path(dictionary["directory"]),
            runs=Path(dictionary["runs"]),
            model=dictionary["model"],
            timeout=int(dictionary["timeout"]),
            commit_hash=dictionary["commit_hash"],
            has_dirty_files=bool(dictionary["has_dirty_files"]),
            executable=Path(dictionary["executable"]),
            flags=dictionary["flags"],
            with_proofs=dictionary.get("with_proofs", False),
        )



def check_runs(context: Context) -> bool:
    wrong_solution_instances = []
    wrong_optimality_instances = []
    num_instances = 0

    with open(INSTANCES[context.model] / "optimal_values.json", "r") as file:
        optimal_values = json.load(file)

    for run in context.runs.iterdir():
        num_instances += 1
        run_status = check_run(run, context.model, optimal_values)
        if run_status is RunError.IncorrectSolution:
            wrong_solution_instances.append(run.stem)
        elif run_status is RunError.IncorrectOptimalSolution:
            wrong_optimality_instances.append(run.stem)
        elif run_status is RunError.Both:
            wrong_solution_instances.append(run.stem)
            wrong_optimality_instances.append(run.stem)

    if len(wrong_solution_instances) > 0:
        print(f"\n{bcolors.FAIL}{len(wrong_solution_instances)}/{num_instances} instances reported at least one incorrect solution{bcolors.ENDC}")
        for errored_instance in wrong_solution_instances:
            print(f"{bcolors.FAIL}\t{errored_instance}{bcolors.ENDC}")
    if len(wrong_optimality_instances) > 0:
        print(f"\n{bcolors.FAIL}{len(wrong_optimality_instances)}/{num_instances} instances reported incorrect optimality{bcolors.ENDC}")
        for wrong_optimality_instance in wrong_optimality_instances:
            print(f"{bcolors.FAIL}\t{wrong_optimality_instance}{bcolors.ENDC}")

    if len(wrong_optimality_instances) > 0 or len(wrong_solution_instances) > 0:
        return False

    return True


def check_run(run: Path, model: ModelType, optimal_values: dict) -> RunError | None:
    instance_name = run.stem

    print(f"Checking {instance_name} for {model}")

    dzn_dir = generate_dzn_instances(run)

    model_path = MINIZINC_MODELS[model]
    data_path = INSTANCES[model] / f"{instance_name}.dzn"

    wrong_optimality = False
    wrong_solution = False

    if is_optimal(run): 
        reported_optimal_value = next((int(line.removeprefix("%%  objective=")) for line in list(iter_solutions(run))[-1].splitlines() if line.startswith("%%  objective=")), None)
        if optimal_values[instance_name] != reported_optimal_value:
            wrong_optimality = True
            print(f"{bcolors.FAIL}Incorrect optimality recorded for {instance_name}; expected {optimal_values[instance_name]} but was {reported_optimal_value}\n{bcolors.ENDC}")

    wrong_solution = run_minizinc(model_path, data_path, dzn_dir)

    if wrong_solution and wrong_optimality:
        return RunError.Both
    elif wrong_solution:
        return RunError.IncorrectSolution
    elif wrong_optimality:
        return RunError.IncorrectOptimalSolution
    else:
        return None


def run_minizinc(model_path: Path, data_path: Path, solutions: Path) -> bool:
    """
        Returns true if there were errors
    """
    error_count = 0
    solution_count = 0

    for instance in solutions.iterdir():
        solution_count += 1
        mzn_command_args = ["minizinc", "--solver", "cp-sat", str(model_path), str(data_path), str(instance)]
        result = run(mzn_command_args, capture_output=True, text=True)

        if result.returncode != 0:
            print("STDOUT:")
            print(result.stdout)

            print("\nSTDERR:")
            print(result.stderr)

            cmd = " ".join(mzn_command_args)
            raise Exception(f"MiniZinc failed. Command: {cmd}")

        if "UNSATISFIABLE" in result.stdout:
            error_count += 1
            print(f"{bcolors.FAIL}Error detected in solution{bcolors.ENDC}")
            print(f"  Solution: {instance.stem}")
            print(f"  Model: {model_path.stem}")
            print(f"  Data: {data_path.stem}")

    if error_count > 0:
        print(f"{bcolors.FAIL}\n{error_count}/{solution_count} solutions had errors.{bcolors.ENDC}")
        return True
    elif solution_count > 0:
        print(f"{bcolors.OKGREEN}All solutions are correct!{bcolors.ENDC}")
        return False
    else:
        print(f"No reported solutions!")
        return False


def iter_solutions(run: Path) -> Iterable[str]:
    """Iterate over the individual solutions of a run."""

    output_log_path = run / "output.log"

    with output_log_path.open('r') as output:
        output = output.read()

    if "UNSATISFIABLE" in output or "UNKNOWN" in output:
        # There are no solutions in this file.
        return iter([])

    return filter(
        lambda s: s != "" and s != OPTIMALITY_PROVEN, 
        map(lambda s: s.strip(), output.split(SOLUTION_SEPARATOR))
    )

def is_optimal(run: Path) -> bool:
    output_log_path = run / "output.log"

    with output_log_path.open('r') as output:
        output = output.read()

    return OPTIMALITY_PROVEN in output


def generate_dzn_instances(run: Path) -> Path:
    """
    For all the reported solutions in this run, generate a DZN file.
    """

    solutions_dir = run / "solutions_dzn"
    if solutions_dir.is_dir():
        # We delete previous solutions if they are generated.
        shutil.rmtree(solutions_dir)

    solutions_dir.mkdir()

    solutions = list(iter_solutions(run))

    print(f"  Identified {len(solutions)} solution(s).")

    for idx, solution in enumerate(solutions):
        solution = solution.strip()

        if solution == "":
            continue

        solution_file = solutions_dir / f"sol-{idx}.dzn"

        with solution_file.open('w') as solution_file:
            for line in solution.split("\n"):
                # Disregard lines (aka variables) that start with an '_' as they are not 
                # variables that correspond to the MZN model.
                if line.startswith("_"):
                    continue

                solution_file.write(f"{line}\n")

    return solutions_dir


@dataclass
class Args:
    """The arguments passed to the evaluation script."""

    model: ModelType
    """The model to evaluate."""

    timeout: int
    """The timeout to give to each instance."""

    flags: List[str]
    """Additional flags provided to the solver."""

    with_proofs: bool
    """If true, scaffolds will be logged."""

    allow_dirty: bool
    """If true, allows uncommitted git changes."""

    explanation_checks: bool
    """If true, enables the explanation checks"""


@dataclass 
class GitStatus:
    has_dirty_files: bool
    commit_hash: str


def get_git_status(args: Args) -> GitStatus | None:
    """
    Get the current git hash of the project. If there are uncommitted changes,
    the program will exit.
    """

    status_result = run(
        ["git", "status", "--porcelain"], 
        capture_output=True, 
        text=True
    )
    if status_result.returncode != 0:
        print(f"Failed to run `git status`")
        print(status_result.stderr)
        return None

    commit_hash_result = run(
        ["git", "rev-parse", "HEAD"], 
        capture_output=True, 
        text=True
    )
    if commit_hash_result.returncode != 0:
        print(f"Failed to run `git rev-parse HEAD`")
        print(commit_hash_result.stderr)
        return None

    commit_hash = commit_hash_result.stdout.strip()

    if len(status_result.stdout) == 0:
        return GitStatus(
            commit_hash=commit_hash, 
            has_dirty_files=False,
        )

    if args.allow_dirty:
        return GitStatus(
            commit_hash=commit_hash, 
            has_dirty_files=True,
        )

    print(f"There are uncommitted changes in the project. Cancelling evaluation.")
    print(f"To ignore this error, run with the '--allow-dirty' flag.")
    return None


def compile_executable(args: Args, experiment_dir: Path) -> Path | None:
    """
    Compiles the executable and returns a Path to it.
    """

    if args.explanation_checks:
        result = run(["cargo", "build", "--release", "--features", "explanation-checks", "--example", args.model])
    else:
        result = run(["cargo", "build", "--release", "--example", args.model])

    if result.returncode != 0:
        # The cargo output is forwarded so no need for an extra message here.
        return None

    on_windows = sys.platform.startswith("win")
    executable_name = f"{args.model}.exe" if on_windows else args.model

    executable_path = Path("target/release/examples/") / executable_name
    shutil.copy2(executable_path, experiment_dir)

    return experiment_dir / executable_name


def initialise(args: Args) -> Context | None:
    """
    Prepare everything for evaluation.
    """

    # Create the directory which stores all the logs, if it does not exist.
    EXPERIMENT_DIR.mkdir(exist_ok=True)

    git_status = get_git_status(args)
    if git_status is None:
        return None

    # Create a directory for the current evaluation.
    timestamp = datetime.now().strftime("%Y%m%d-%H.%M.%S.%f")
    directory = EXPERIMENT_DIR / f"{timestamp}-{args.model}"

    try:
        directory.mkdir()
    except FileExistsError:
        print("Error creating evaluation context directory. Please try again.")
        return None

    # Create the directory which will contain all the solver logs.
    runs = directory / "runs"
    runs.mkdir()

    executable = compile_executable(args, directory)
    if executable is None:
        return None

    context = Context(
        directory=directory, 
        runs=runs,
        model=args.model,
        timeout=args.timeout,
        commit_hash=git_status.commit_hash,
        executable=executable,
        flags=args.flags,
        has_dirty_files=git_status.has_dirty_files,
        with_proofs=args.with_proofs,
    )

    with (directory / "manifest.json").open('w') as context_file:
        json.dump(context.to_dict(), context_file, indent=4)

    return context


def run_instances(context: Context):
    instances = INSTANCES[context.model]

    for instance in instances.glob("*.dzn"):
        run_instance(instance, context)


def run_instance(instance: Path, context: Context):
    print(f"Evaluating instance {instance.stem}")

    instance_directory = context.runs / instance.stem
    instance_directory.mkdir()

    log_file_path = instance_directory / "output.log"
    err_file_path = instance_directory / "output.err"

    proof_args = ["-P", instance_directory / "scaffold.drcp"] if context.with_proofs else []

    with log_file_path.open('w') as log_file:
        with err_file_path.open('w') as err_file:
            run(
                [context.executable, instance, "solve", *proof_args, *context.flags, str(context.timeout)],
                stdout=log_file,
                stderr=err_file,
            ) 


def evaluate(args: Args) -> Context | None:
    context = initialise(args)
    if context is None:
        return None

    run_instances(context)
    return context
