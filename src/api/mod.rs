mod outputs;
pub(crate) mod solver;

pub mod results {
    //! Contains the outputs of solving using the [`Solver`].
    //!
    //! We differentiate between 3 different types of results:
    //! - For a **satisfaction** problem ([`SatisfactionResult`])
    //! - For a **satisfaction** problem using **assumptions**
    //!   ([`SatisfactionResultUnderAssumptions`])
    //! - For an **optimisation** problem ([`OptimisationResult`])
    //!
    //! On these results, different methods can be called which ensure that the solver is in the
    //! right state for these operations. For example,
    //! [`SatisfactionResultUnderAssumptions::UnsatisfiableUnderAssumptions`] allows you to extract
    //! a core consisting of the assumptions using [`UnsatisfiableUnderAssumptions::extract_core`].
    pub use crate::api::outputs::solution_iterator;
    pub use crate::api::outputs::unsatisfiable;
    pub use crate::api::outputs::OptimisationResult;
    pub use crate::api::outputs::ProblemSolution;
    pub use crate::api::outputs::SatisfactionResult;
    pub use crate::api::outputs::SatisfactionResultUnderAssumptions;
    pub use crate::api::outputs::SolutionReference;
    pub use crate::basic_types::Solution;
    #[cfg(doc)]
    use crate::results::unsatisfiable::UnsatisfiableUnderAssumptions;
    #[cfg(doc)]
    use crate::Solver;
}

pub mod variables {
    //! Contains the variables which are used by the [`Solver`].
    //!
    //! A variable, in the context of the solver, is a view onto a domain. It may forward domain
    //! information unaltered, or apply transformations which can be performed without the need of
    //! constraints.
    //!
    //! We define 2 types of variables:
    //! - Integer Variables ([`IntegerVariable`]) - These are represented by [`DomainId`]s when
    //!   interacting with the [`Solver`]. These variables can be created using
    //!   [`Solver::new_bounded_integer`] when creating a variable with the domain between a
    //!   lower-bound and an upper-bound or using [`Solver::new_sparse_integer`] when creating a
    //!   variable with holes in the domain. These variables can be transformed (according to the
    //!   trait [`TransformableVariable`]) to create an [`AffineView`].
    //! - Propositional Variables ([`PropositionalVariable`]) - These specify booleans that can be
    //!   used when interacting with the [`Solver`]. A [`Literal`] is used when a
    //!   [`PropositionalVariable`] is given a polarity (i.e. it is the positive [`Literal`] or its
    //!   negated version). A [`Literal`] can be created using [`Solver::new_literal`].
    pub use crate::engine::variables::AffineView;
    pub use crate::engine::variables::DomainId;
    pub use crate::engine::variables::IntegerVariable;
    pub use crate::engine::variables::Literal;
    pub use crate::engine::variables::PropositionalVariable;
    pub use crate::engine::variables::TransformableVariable;
    #[cfg(doc)]
    use crate::Solver;
}

pub mod options {
    //! Contains the options which can be passed to the [`Solver`].
    //!
    //! These influence the following aspects:
    //! - The restart strategy of the solver
    //! - The learned clause database management approach
    //! - The proof logging
    pub use crate::engine::SatisfactionSolverOptions as SolverOptions;
    #[cfg(doc)]
    use crate::Solver;
}

pub mod termination {
    //! Contains the conditions which are used to determine when the [`Solver`] should terminate
    //! even when the state of the satisfaction/optimization problem is unknown.
    //!
    //! The main [`TerminationCondition`] is a condition which is polled by the [`Solver`] during
    //! the search process. It indicates when the [`Solver`] should stop, even if no definitive
    //! conclusions have been made.
    //!
    //! The most common example would be [`TimeBudget`], which terminates the [`Solver`] whenever
    //! the time budget is exceeded.
    pub use crate::engine::termination::combinator::*;
    pub use crate::engine::termination::indefinite::*;
    pub use crate::engine::termination::os_signal::*;
    pub use crate::engine::termination::time_budget::*;
    pub use crate::engine::termination::TerminationCondition;
    #[cfg(doc)]
    use crate::Solver;
}

pub mod statistics {
    //! Contains functions which configure the logging and allow the logging of statistics
    //! themselves.
    pub use crate::basic_types::statistic_logging::statistic_logger::*;
}

pub mod predicates {
    //! Containts structures which represent certain [predicates](https://en.wikipedia.org/wiki/Predicate_(mathematical_logic)).
    //!
    //! The solver only utilizes the following types of predicates:
    //! - **Predicates over integers** - These [`IntegerPredicate`]s specify atomic constraints of
    //!   the form `[x >= v]`, `[x <= v]`, `[x == v]`, and `[x != v]`.
    //! - **Predicates over literals** - These [`Predicate::Literal`]s specify [`Literal`]s which
    //!   are linked to the aforementioned [`IntegerPredicate`]s.
    //! - **Always True/False** - The [`Predicate::True`]/[`Predicate::False`] specify logical
    //!   predicates which are always true/false.
    //!
    //! In general, these [`Predicate`]s are used to represent propagations, explanations or
    //! decisions.
    pub use crate::basic_types::PropositionalConjunction;
    pub use crate::engine::predicates::integer_predicate::IntegerPredicate;
    pub use crate::engine::predicates::predicate::Predicate;
    pub use crate::engine::predicates::predicate_constructor::PredicateConstructor;
    #[cfg(doc)]
    use crate::variables::Literal;
}
