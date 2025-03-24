#!/usr/bin/env python3
import subprocess

from common import Args, ModelType, check_runs, evaluate

def flatten(foo):
    result = []
    for x in foo:
        if hasattr(x, '__iter__') and not isinstance(x, str):
            for y in flatten(x):
               result.append(y) 
        else:
            result.append(x)
    return result

MODELS = ["tsp", "rcpsp", "cluster_editing"]

# Timeout per instance.
INSTANCE_TIMEOUT = 20

OPTIMISATION_TEST_MODULES = {
        "linear-unsat-sat": "linear_unsat_sat",
        "oll": "oll",
        "ihs": "implicit_hitting_sets",
}

OPTIMISATION_CONTRIBUTION = {
        "linear-unsat-sat": 10,
        "oll": 12,
        "ihs": 18
}

OPTIMISATION_MODELS = {
    "linear-unsat-sat": ["rcpsp", "tsp", "cluster_editing"],
    "oll": ["rcpsp", "cluster_editing"],
    "ihs": ["rcpsp", "cluster_editing"]
}

CORE_MINIMISATION_TEST_MODULE = "core_minimisation"
CORE_MINIMISATION_CONTRIBUTION = 5 


def grade_optimisation(optimisation: str, model: ModelType, first_run=False) -> bool:
    """Grade an optimisation procedure given the optimisation strategy and model. Return the contribution to the final grade for this optimisation procedure."""

    if first_run:
        test_filter = f"tests::optimisation::{OPTIMISATION_TEST_MODULES[optimisation]}"
        result = subprocess.run(
            ["cargo", "test", test_filter],
            capture_output=True,
            text=True,
        )

        if result.returncode != 0:
            print(result.stdout)
            return False 

    context = evaluate(Args(
        model=model,
        timeout=INSTANCE_TIMEOUT,
        flags=["-O", optimisation],
        allow_dirty=True,
    ))
    if context is None:
        return False

    if not check_runs(context):
        return False

    return True

def grade_core_minimisation() -> int:
    """Grade core minimisation by running the unit tests and running it on the cluster editing model using OLL. Return the contribution to the final grade for core minimisation."""

    test_filter = f"tests::optimisation::{CORE_MINIMISATION_TEST_MODULE}"
    result = subprocess.run(
        ["cargo", "test", test_filter],
        capture_output=True,
        text=True,
    )

    if result.returncode != 0:
        print(result.stdout)
        return 0 

    context = evaluate(Args(
        model="cluster_editing",
        timeout=INSTANCE_TIMEOUT,
        flags=["-O", "oll"],
        allow_dirty=True,
    ))
    if context is None:
        return 0 

    if not check_runs(context):
        return 0

    return CORE_MINIMISATION_CONTRIBUTION 

def run():
    max_grade = sum(OPTIMISATION_CONTRIBUTION.values()) + CORE_MINIMISATION_CONTRIBUTION 
    assert max_grade == 45, \
        f"Expected the maximum total grade to be 45 points. Was {max_grade}"

    optimisation_approaches = OPTIMISATION_TEST_MODULES.keys()

    total_grade = 0
    passed = []
    failed = []

    for optimisation in optimisation_approaches:
        passed_tests = True 
        print(f"\nGrading {optimisation}")
        for (index, model) in enumerate(OPTIMISATION_MODELS[optimisation]):
            passed_tests &= grade_optimisation(optimisation, model, first_run=index==0)
        if passed_tests:
            total_grade += OPTIMISATION_CONTRIBUTION[optimisation]
            passed.append(optimisation)
            print(f"  Passes all tests!")
        else:
            failed.append(optimisation)
            print(f"  {optimisation} failed on one of the models")

    print(f"\nGrading core minimisation")
    core_minimisation = grade_core_minimisation()
    total_grade += core_minimisation 
    if core_minimisation == 0:
        failed.append("Core minimisation")
        print(f"  Core Minimisation failed")
    else:
        print(f"  Passes core minimisation tests!")

    print(f"\nGrade = {total_grade}% / {max_grade}%")
    print(f"  Passed: {passed}")
    print(f"  Failed: {failed}")


if __name__ == "__main__":
    run()
