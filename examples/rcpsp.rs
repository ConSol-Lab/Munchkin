use std::collections::HashSet;

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

munchkin::entry_point!(problem = Rcpsp, search_strategies = SearchStrategies);

#[derive(Clone, Copy, Default, ValueEnum)]
enum SearchStrategies {
    #[default]
    Default,
}

struct Rcpsp {
    start_times: IntVariableArray,
    makespan: IntVariable,
}

impl Problem<SearchStrategies> for Rcpsp {
    fn create(data: DataFile<i32>) -> anyhow::Result<(Self, Model)> {
        let mut model = Model::default();

        let num_resources = data
            .get::<i32>("n_res")
            .copied()
            .ok_or_else(|| anyhow::anyhow!("Missing int 'n_res' in data file."))?;
        let num_resources_usize = usize::try_from(num_resources)?;

        let num_tasks = data
            .get::<i32>("n_tasks")
            .copied()
            .ok_or_else(|| anyhow::anyhow!("Missing int 'n_tasks' in data file."))?;
        let num_tasks_usize = usize::try_from(num_tasks)?;

        let durations = data
            .array_1d::<i32>("d", num_tasks_usize)
            .ok_or_else(|| anyhow::anyhow!("Missing int array 'd' in data file."))?;
        let durations: Vec<_> = iterate(durations)
            .copied()
            .map(u32::try_from)
            .collect::<Result<_, _>>()?;

        let resource_requirements = data
            .array_2d::<i32>("rr", [num_resources_usize, num_tasks_usize])
            .ok_or_else(|| anyhow::anyhow!("Missing 2d int array 'rr' in data file."))?;

        let resource_capacities = data
            .array_1d::<i32>("rc", num_resources_usize)
            .ok_or_else(|| anyhow::anyhow!("Missing int array 'rc' in data file."))?;

        let successors = data
            .array_1d::<HashSet<i32>>("suc", num_tasks_usize)
            .ok_or_else(|| anyhow::anyhow!("Missing set of int array 'suc' in data file."))?;

        let horizon = durations.iter().sum::<u32>() as i32;

        let start_times = model.new_interval_variable_array("Start", 0, horizon, num_tasks_usize);

        for resource in 0..num_resources_usize {
            let resource_capacity = resource_capacities
                .get([resource])
                .copied()
                .unwrap()
                .try_into()?;

            let resource_requirements: Vec<_> = slice_row(resource_requirements, resource)
                .into_iter()
                .map(u32::try_from)
                .collect::<Result<_, _>>()?;

            let start_times = start_times.as_array(&model).collect();
            model.add_constraint(Constraint::Cumulative {
                start_times,
                durations: durations.clone(),
                resource_requirements,
                resource_capacity,
            });
        }

        let start_times_array: Vec<_> = start_times.as_array(&model).collect();
        for task in 0..num_tasks_usize {
            let task_successors = successors.get([task]).unwrap();

            for successor in task_successors.iter() {
                // The instance is 1-indexed.
                let successor = *successor as usize - 1;

                // Start[task] + Duration[task] <= Start[successor]
                model.add_constraint(Constraint::LinearLessEqual {
                    terms: vec![
                        start_times_array[task],
                        start_times_array[successor].scaled(-1),
                    ],
                    rhs: -(durations[task] as i32),
                });
            }
        }

        let makespan = model.new_interval_variable("Objective", 0, horizon);
        model.add_constraint(Constraint::Maximum {
            terms: start_times_array
                .iter()
                .enumerate()
                .map(|(task, start_time)| start_time.offset(durations[task] as i32))
                .collect(),
            rhs: makespan,
        });

        Ok((
            Rcpsp {
                start_times,
                makespan,
            },
            model,
        ))
    }

    fn objective(&self) -> IntVariable {
        self.makespan
    }

    fn get_search(
        &self,
        strategy: SearchStrategies,
        _: &Solver,
        solver_variables: &VariableMap,
    ) -> impl Brancher + 'static {
        match strategy {
            #[allow(
                trivial_casts,
                reason = "without it, the type-checker cannot infer that `dyn Brancher` impls `Brancher`"
            )]
            SearchStrategies::Default => Box::new(IndependentVariableValueBrancher::new(
                InputOrder::new(
                    solver_variables
                        .get_array(self.start_times)
                        .into_iter()
                        .chain([solver_variables.to_solver_variable(self.makespan)])
                        .collect(),
                ),
                InDomainMin,
            )) as Box<dyn Brancher>,
        }
    }

    fn get_output_variables(&self) -> impl Iterator<Item = Output> + '_ {
        [
            Output::Array(self.start_times),
            Output::Variable(self.makespan),
        ]
        .into_iter()
    }
}

fn iterate<T>(array: &ShapedArray<T, 1>) -> impl Iterator<Item = &T> {
    let [len] = *array.shape();

    (0..len).map(|i| array.get([i]).unwrap())
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
