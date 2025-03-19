# Munchkin
A minimal lazy clause generation constraint solver written in Rust used for teaching

## Running Models
Models are implemented as [Cargo Examples](https://doc.rust-lang.org/cargo/reference/cargo-targets.html#examples). Each model has a documented help section which describes all the options you can provide. An example of how you can run a model would be:

```
$ cargo run --example tsp -- data/tsp/TSP_N5_0.dzn solve 10
```

To specify a global, the `--global` flag can be used. This flag can be provided multiple times to enable multiple globals. For example:

```
$ cargo run --example tsp -- data/tsp/TSP_N5_0.dzn solve --global dfs-circuit --global all-different 10
```
For the linear constraint, the solver can also be instructed to use an encoding. Supply the `--linear-encoding` flag to specify which encoding to use.

## Provided Scripts
We have provided scripts to help with the evaluation of your implementation. These can be found in the `scripts` directory.

> [!IMPORTANT]
> All scripts assume they are execute from the project root, i.e. the directory which contains this README file.

### Evaluation
To evaluate a model on all the instances, the `evaluate` script can be used. Provide it the name of the model and a timeout, as well as flags you want to pass on to the underlying binary, such as globals.

An example of the command would be:
```
$ python3 scripts/evaluate.py tsp 10 --global dfs-circuit
```
This will create the folder `experiments`, and inside it place the directory which has all the data for this particular evaluation.


### Solution Checking
After having evaluated your model, the solutions can be checked using the `check-solutions` script. Provide it with a specific experiment folder and it will indicate if your solutions are incorrect, or wether an incorrect optimal solution is reported.

An example of the command would be:
```
$ python3 scripts/check-solutions.py experiments/<timestamp>-tsp
```

> [!IMPORTANT]
> Solution checking is done using [MiniZinc](https://minizinc.org). Make sure you have it installed and available on your PATH.

### Statistic Parsing
The `parse-data` script can be used to aggregate the statistics for all the runs into a single CSV file for an evaluation. It will generate a CSV with a row for each instance, containing solver statistics.

An example of the command would be:
```
$ python3 scripts/parse-data.py experiments/<timestamp>-tsp
```
