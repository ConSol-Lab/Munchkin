use std::num::NonZero;

use clap::Parser;
use munchkin::branching::branchers::independent_variable_value_brancher::IndependentVariableValueBrancher;
use munchkin::branching::InDomainMin;
use munchkin::branching::InputOrder;
use munchkin::constraints;
use munchkin::results::ProblemSolution;
use munchkin::results::SatisfactionResult;
use munchkin::termination::Indefinite;
use munchkin::variables::TransformableVariable;
use munchkin::Solver;

#[derive(Debug, Parser)]
struct Cli {
    /// The size of the puzzle. Should be an integer greater than 1.
    #[arg(value_parser = clap::value_parser!(i32).range(2..))]
    n: i32,
}

fn main() {
    let Cli { n } = Cli::parse();

    let mut solver = Solver::default();

    // The q_i variables
    let variables = (0..n)
        .map(|_| solver.new_bounded_integer(0, n - 1))
        .collect::<Vec<_>>();

    // The [q_i + i | 0 <= i < n] variables
    let diag1 = variables
        .iter()
        .cloned()
        .enumerate()
        .map(|(i, var)| var.offset(i as i32))
        .collect::<Vec<_>>();

    // The [q_i - i | 0 <= i < n] variables
    let diag2 = variables
        .iter()
        .cloned()
        .enumerate()
        .map(|(i, var)| var.offset(-(i as i32)))
        .collect::<Vec<_>>();

    let _ = solver
        .add_constraint(constraints::all_different_decomposition(variables.clone()))
        .post(NonZero::new(1).unwrap());
    let _ = solver
        .add_constraint(constraints::all_different_decomposition(diag1))
        .post(NonZero::new(2).unwrap());
    let _ = solver
        .add_constraint(constraints::all_different_decomposition(diag2))
        .post(NonZero::new(3).unwrap());

    let mut brancher =
        IndependentVariableValueBrancher::new(InputOrder::new(variables.clone()), InDomainMin);

    match solver.satisfy(&mut brancher, &mut Indefinite) {
        SatisfactionResult::Satisfiable(solution) => {
            let row_separator = format!("{}+", "+---".repeat(n as usize));

            for row in 0..n {
                println!("{row_separator}");

                let queen_col = solution.get_integer_value(variables[row as usize]);

                for col in 0..n {
                    let string = if queen_col == col { "| * " } else { "|   " };

                    print!("{string}");
                }

                println!("|");
            }

            println!("{row_separator}");
        }
        SatisfactionResult::Unsatisfiable => {
            println!("{n}-queens is unsatisfiable.");
        }
        SatisfactionResult::Unknown => {
            println!("Timeout.");
        }
    }
}
