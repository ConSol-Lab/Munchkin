use std::collections::HashSet;

use clap::ValueEnum;
use dzn_rs::DataFile;
use munchkin::branching::branchers::independent_variable_value_brancher::IndependentVariableValueBrancher;
use munchkin::branching::Brancher;
use munchkin::branching::InDomainMin;
use munchkin::branching::InputOrder;
use munchkin::model::Constraint;
use munchkin::model::IntVariable;
use munchkin::model::Model;
use munchkin::model::Output;
use munchkin::model::TwoDimensionalIntVariableArray;
use munchkin::model::VariableMap;
use munchkin::runner::Problem;
use munchkin::Solver;

munchkin::entry_point!(
    problem = ClusterEditing,
    search_strategies = SearchStrategies
);

#[derive(Clone, Copy, Default, ValueEnum)]
enum SearchStrategies {
    #[default]
    Default,
}

struct ClusterEditing {
    are_in_same_cluster: TwoDimensionalIntVariableArray,
    cost: IntVariable,
    objective_elements: Vec<IntVariable>,
}

impl Problem<SearchStrategies> for ClusterEditing {
    fn create(data: DataFile<i32>) -> anyhow::Result<(Self, Model)> {
        let mut model = Model::default();

        let num_nodes = data
            .get::<i32>("n_nodes")
            .copied()
            .ok_or_else(|| anyhow::anyhow!("Missing int 'n_res' in data file."))?;
        let num_nodes_usize = usize::try_from(num_nodes)?;

        let edges = data
            .array_1d::<HashSet<i32>>("edges", num_nodes_usize)
            .ok_or_else(|| anyhow::anyhow!("Missing set of int array 'suc' in data file."))?;

        // We create variables indicating whether i and j are in the same cluster
        let are_in_same_cluster =
            model.new_interval_variable_matrix("x", 0, 1, num_nodes_usize, num_nodes_usize);

        // First we add a transitivity constraint stating that if i and j are
        for i in 0..num_nodes_usize {
            for j in 0..num_nodes_usize {
                for k in 0..num_nodes_usize {
                    let x_ij = are_in_same_cluster.get(&model, i, j);
                    let x_jk = are_in_same_cluster.get(&model, j, k);
                    let x_ik = are_in_same_cluster.get(&model, i, k);
                    model.add_constraint(Constraint::LinearLessEqual {
                        terms: vec![x_ij, x_jk, x_ik.scaled(-1)],
                        rhs: 1,
                    });
                }
            }
        }

        let cost = model.new_interval_variable(
            "Objective",
            0,
            (num_nodes_usize * (num_nodes_usize - 1)) as i32,
        );
        let terms = (0..num_nodes_usize)
            .flat_map(|i| {
                (0..num_nodes_usize)
                    .map(|j| {
                        if edges.get([i]).unwrap().contains(&((j + 1) as i32)) {
                            are_in_same_cluster.get(&model, i, j).scaled(-1).offset(1)
                        } else {
                            are_in_same_cluster.get(&model, i, j)
                        }
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        model.add_constraint(Constraint::LinearEqual {
            terms: terms
                .clone()
                .into_iter()
                .chain(std::iter::once(cost.scaled(-1)))
                .collect::<Vec<_>>(),
            rhs: 0,
        });

        Ok((
            ClusterEditing {
                are_in_same_cluster,
                cost,
                objective_elements: terms,
            },
            model,
        ))
    }

    fn objective(&self) -> IntVariable {
        self.cost
    }

    fn get_search(
        &self,
        strategy: SearchStrategies,
        _: &Solver,
        solver_variables: &VariableMap,
    ) -> impl Brancher + 'static {
        match strategy {
            SearchStrategies::Default => Box::new(IndependentVariableValueBrancher::new(
                InputOrder::new(
                    solver_variables
                        .get_matrix(self.are_in_same_cluster)
                        .into_iter()
                        .flatten()
                        .chain(std::iter::once(
                            solver_variables.to_solver_variable(self.cost),
                        ))
                        .collect::<Vec<_>>(),
                ),
                InDomainMin,
            )) as Box<dyn Brancher>,
        }
    }

    fn get_output_variables(&self) -> impl Iterator<Item = Output> + '_ {
        [
            Output::TwoDimensionalArray(self.are_in_same_cluster),
            Output::Variable(self.cost),
        ]
        .into_iter()
    }

    fn objective_function(&self) -> Vec<IntVariable> {
        self.objective_elements.clone()
    }
}
