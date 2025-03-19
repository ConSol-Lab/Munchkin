#!/usr/bin/env python3

from argparse import ArgumentParser
import csv
import json
from pathlib import Path
from subprocess import run

from common import *


def process_proof(context: Context, run_dir: Path):
    instance_name = run_dir.name
    instance = INSTANCES[context.model] / f"{instance_name}.dzn"

    log_file_path = run_dir / "process.log"
    err_file_path = run_dir / "process.err"

    scaffold_path = run_dir / "scaffold.drcp"
    proof_path = run_dir / "full_proof.drcp"

    if not scaffold_path.is_file():
        print("Missing {scaffold_path}")
        print("  Did you solve with proof logging enabled?")
        return

    with log_file_path.open('w') as log_file:
        with err_file_path.open('w') as err_file:
            run(
                [context.executable, instance, "process", scaffold_path, proof_path],
                stdout=log_file,
                stderr=err_file,
            ) 


def check_proof(context: Context, run_dir: Path):
    instance_name = run_dir.name
    instance = INSTANCES[context.model] / f"{instance_name}.dzn"

    log_file_path = run_dir / "checking.log"
    err_file_path = run_dir / "checking.err"

    proof_path = run_dir / "full_proof.drcp"
    if not proof_path.is_file():
        print("Missing {proof_path}")
        print("  Did you process the proofs?")
        return

    with log_file_path.open('w') as log_file:
        with err_file_path.open('w') as err_file:
            result = run(
                [context.executable, instance, "check", proof_path],
                stdout=log_file,
                stderr=err_file,
            ) 

    check_return_code = result.returncode
    
    check_status_file = run_dir / "checking_status"
    with check_status_file.open('w') as f:
        f.write(str(check_return_code))


def run_script(experiment_dir: Path, action: str):
    with (experiment_dir / "manifest.json").open('r') as manifest:
        context = Context.from_dict(json.load(manifest))

    statistics_path = experiment_dir / "statistics.csv"
    if not statistics_path.is_file():
        print("First parse the log data with 'parse-data.py'")
        sys.exit(1)

    num_proofs_processed = 0

    with statistics_path.open('r') as f:
        reader = csv.reader(f)

        header = next(reader)

        for row in reader:
            assert len(header) == len(row), "Malformed CSV: Not all rows are equal length"

            row_dict = {k: v for k, v in zip(header, row)}

            if row_dict["status"] != "OPTIMAL":
                continue

            num_proofs_processed += 1

            if action == "process":
                process_proof(context, experiment_dir / "runs" / row_dict["instance"])
            elif action == "check":
                check_proof(context, experiment_dir / "runs" / row_dict["instance"])


if __name__ == "__main__":
    arg_parser = ArgumentParser(description="Check the solutions for an experiment.")

    arg_parser.add_argument("experiment_dir", type=Path, help="The directory containing the experiment data.")
    arg_parser.add_argument("action", choices=["process", "check"], help="The action to perform given the proof.")

    args = arg_parser.parse_args()

    run_script(args.experiment_dir, args.action)

