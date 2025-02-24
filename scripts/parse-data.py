#!/usr/bin/env python3
from argparse import ArgumentParser
from dataclasses import dataclass
from pathlib import Path
from common import *
import csv
import json


STATISTICS = [
    "instance",
    "status",
    "objective",
    "numberOfDecisions",
    "numberOfConflicts",
    "numberOfPropagations",
    "timeSpentInSolverInMilliseconds",
    "averageBacktrackAmount",
    "averageSizeOfConflictExplanation",
    "numberOfLearnedUnitNogoods",
    "averageLearnedNogoodLength",
    "averageLearnedNogoodLbd",
];



@dataclass
class Args:
    """Commandline arguments for this script."""

    experiment_dir: Path
    """The directory of the experiment."""


def run(args: Args):
    with (args.experiment_dir / "manifest.json").open('r') as manifest:
        context = Context.from_dict(json.load(manifest))

    with (context.directory / "statistics.csv").open('w') as csvfile:
        writer = csv.writer(csvfile)

        writer.writerow(STATISTICS)

        for run in context.runs.iterdir():
            run_data = parse_run(run)
            writer.writerow([run_data.get(stat, "-") for stat in STATISTICS])


def parse_run(run: Path):
    print(f"Parsing {run.stem}")

    # Read the output of the run.
    with (run / "output.log").open('r') as log:
        output = log.read().strip()

    # Trim off the optimality marker if it exists.
    if output.endswith(OPTIMALITY_PROVEN):
        optimal = True
        output = output[:-len(OPTIMALITY_PROVEN)].strip()
    else:
        optimal = False

    # Trim off the trailing solution separator if it exists.
    if output.endswith(SOLUTION_SEPARATOR):
        has_solution = True
        output = output[:-len(SOLUTION_SEPARATOR)].strip()
    else:
        has_solution = False

    is_unsatisfiable = "UNSATISFIABLE" in output

    # If there are multiple solutions, disregard all output except for the last reported
    # batch of statistics.
    splits = output.rsplit(SOLUTION_SEPARATOR, 1)
    if len(splits) == 1:
        # In case the result is UNSAT or UNKNOWN, `splits` will be length 1.
        result = splits[0].strip()
    else:
        result = splits[1].strip()

    stats = {
        "instance": run.stem,
        "status": "OPTIMAL" if optimal else "SATISFIABLE" if has_solution else "UNSATISFIABLE" if is_unsatisfiable else "UNKNOWN"
    }

    for line in result.splitlines():
        if not line.startswith("%% "):
            continue

        line = line.removeprefix("%% ").strip()

        stat_name, value = line.split('=')
        stats[stat_name] = int(value)

    return stats



if __name__ == "__main__":
    arg_parser = ArgumentParser(description="Parse the statistics from all runs into a CSV.")

    arg_parser.add_argument("experiment_dir", type=Path, help="The directory containing the experiment data.")

    args = arg_parser.parse_args()

    run(Args(experiment_dir=args.experiment_dir))
