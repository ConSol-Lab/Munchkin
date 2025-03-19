#!/usr/bin/env python3

from argparse import ArgumentParser
from dataclasses import dataclass
from subprocess import run
import json
from common import *


@dataclass
class Args:
    """The command line arguments."""

    model: ModelType


def compute_optimal_values(args: Args):
    instances = INSTANCES[args.model]

    model_path = MINIZINC_MODELS[args.model]

    optimal_values = {}

    for instance in instances.glob("*.dzn"):
        print(f"Computing {instance.stem}")
        result = run(
            ["minizinc", "--output-objective", "--output-mode", "dzn", "--solver", "cp-sat", "-f", model_path, instance], 
            capture_output=True, 
            text=True
        )

        if result.returncode != 0:
            print("Failed to run minizinc.")
            print("STDOUT:")
            print(result.stdout)
            print("STDERR:")
            print(result.stderr)
            return

        objective_line = next(
            (line for line in result.stdout.splitlines() if line.startswith("_objective")), 
            None
        )

        if objective_line is None:
            print("Failed to extract objective from MiniZinc.")
            print("STDOUT:")
            print(result.stdout)
            return

        objective_value = int(objective_line.removeprefix("_objective = ").removesuffix(";"))
        print(f"  Optimal objective = {objective_value}")
        optimal_values[instance.stem] = objective_value


    with (instances / "optimal_values.json").open('w') as file:
        json.dump(optimal_values, file, indent=4)



if __name__ == "__main__":
    arg_parser = ArgumentParser()

    arg_parser.add_argument("model", choices=MINIZINC_MODELS.keys(), help="The model to get the optimal values for.")

    args = arg_parser.parse_args()

    compute_optimal_values(Args(model=args.model))
