//! Sets up munchkin with a model for the travelling salesperson problem.
//!
//! # Model
//! ```mzn
//! % The number of nodes in the graph.
//! int: N;
//!
//! % The distance matrix between every pair of nodes.
//! array [1..N, 1..N] of int: Dist;
//!
//! % `Successor[i]` denotes the node which succeeds the node `i`.
//! array [1..N] of var 1..N: Successor;
//!
//! % Enforce a Hamiltonian cycle.
//! constraint circuit(Successor);
//!
//! % Optimize for the shortest tour length.
//! solve minimize sum([Dist[node, Successor[node]] | node in 1..N]);
//! ```

use clap::ValueEnum;
use dzn_rs::DataFile;
use dzn_rs::ShapedArray;
use munchkin::branching::branchers::independent_variable_value_brancher::IndependentVariableValueBrancher;
use munchkin::branching::Brancher;
use munchkin::branching::InDomainMin;
use munchkin::branching::InputOrder;
use munchkin::model::Constraint;
use munchkin::model::IntVariable;
use munchkin::model::IntVariableArray;
use munchkin::model::Model;
use munchkin::model::Output;
use munchkin::model::VariableMap;
use munchkin::runner::Problem;
use munchkin::Solver;

munchkin::entry_point!(
    problem = TravellingSalesperson,
    search_strategies = SearchStrategies
);

#[derive(Clone, Default, ValueEnum)]
enum SearchStrategies {
    #[default]
    Default,
}

struct TravellingSalesperson {
    successors: IntVariableArray,
    /// For every node, there is a variable for the cost of leaving that node to go to its
    /// successor.
    outgoing_costs: IntVariableArray,
    /// The total cost of the tour.
    objective: IntVariable,
}

impl Problem<SearchStrategies> for TravellingSalesperson {
    fn create(data: DataFile<i32>) -> anyhow::Result<(Self, Model)> {
        let mut model = Model::default();

        let (n, dist) = extract_data(&data)?;

        let successors = model.new_interval_variable_array("Successor", 1, n, n as usize);
        let successors_array: Vec<_> = successors.as_array(&model).collect();

        model.add_constraint(Constraint::Circuit(successors.as_array(&model).collect()));

        // The upper bound for the objective variable is a very lax upper bound, as it
        // is a summation over all elements in the distance matrix.
        let max_objective = iterate(dist).sum();
        let objective = model.new_interval_variable("Objective", 0, max_objective);

        let outgoing_costs = model.new_interval_variable_array(
            "_OutgoingCost",
            0,
            iterate(dist).max().unwrap(),
            n as usize,
        );
        let outgoing_costs_array: Vec<_> = outgoing_costs.as_array(&model).collect();

        successors_array
            .iter()
            .enumerate()
            .for_each(|(node, successor)| {
                // The costs of going from `node` to any of the other nodes.
                let distances_from_node = slice_row(dist, node)
                    .into_iter()
                    .enumerate()
                    .map(|(idx, dist)| {
                        model.new_interval_variable(
                            format!("_Dist[{node}][{}]_eq_{dist}", idx + 1),
                            dist,
                            dist,
                        )
                    })
                    .collect();

                // Constrain the `outgoing_cost` to be the distance between `node` and its
                // successor.
                model.add_constraint(Constraint::Element {
                    array: distances_from_node,
                    index: *successor,
                    rhs: outgoing_costs_array[node],
                });
            });

        // `\sum outgoing_costs = objective` <-> `\sum {outgoing_costs} - objective = 0`
        model.add_constraint(Constraint::LinearEqual {
            terms: outgoing_costs_array
                .iter()
                .copied()
                .chain(std::iter::once(objective.scaled(-1)))
                .collect(),
            rhs: 0,
        });

        Ok((
            TravellingSalesperson {
                successors,
                outgoing_costs,
                objective,
            },
            model,
        ))
    }

    fn objective(&self) -> IntVariable {
        self.objective
    }

    fn get_search(
        &self,
        strategy: SearchStrategies,
        _: &Solver,
        variables: &VariableMap,
    ) -> impl Brancher + 'static {
        match strategy {
            #[allow(
                trivial_casts,
                reason = "without it, the type-checker cannot infer that `dyn Brancher` impls `Brancher`"
            )]
            SearchStrategies::Default => Box::new(IndependentVariableValueBrancher::new(
                InputOrder::new(variables.get_array(self.successors)),
                InDomainMin,
            )) as Box<dyn Brancher>,
        }
    }

    fn get_output_variables(&self) -> impl Iterator<Item = Output> + '_ {
        [
            Output::Array(self.successors),
            Output::Array(self.outgoing_costs),
            Output::Variable(self.objective),
        ]
        .into_iter()
    }
}

fn extract_data(data: &DataFile<i32>) -> anyhow::Result<(i32, &ShapedArray<i32, 2>)> {
    let n: i32 = data
        .get("N")
        .copied()
        .ok_or_else(|| anyhow::anyhow!("Missing int parameter 'N' in data."))?;

    let n_usize: usize = n
        .try_into()
        .map_err(|_| anyhow::anyhow!("'N' should be an unsigned integer."))?;
    let dist = data
        .array_2d::<i32>("Dist", [n_usize, n_usize])
        .ok_or_else(|| anyhow::anyhow!("Missing 2d int array 'dist'."))?;

    Ok((n, dist))
}

/// Extract a row from the 2d array.
fn slice_row(array: &ShapedArray<i32, 2>, row: usize) -> Vec<i32> {
    let [_, n_cols] = *array.shape();

    (0..n_cols)
        .map(move |col| {
            array
                .get([row, col])
                .copied()
                .expect("index is within range")
        })
        .collect()
}

/// Iterate over the elements in `array`.
fn iterate(array: &ShapedArray<i32, 2>) -> impl Iterator<Item = i32> + '_ {
    let [n_rows, n_cols] = *array.shape();

    (0..n_rows)
        .flat_map(move |row| (0..n_cols).map(move |col| array.get([row, col]).copied().unwrap()))
}
