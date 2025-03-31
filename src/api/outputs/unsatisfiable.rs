//! Contains the representation of a unsatisfiable solution.

use crate::branching::Brancher;
use crate::engine::ConstraintSatisfactionSolver;
#[cfg(doc)]
use crate::Solver;

/// A struct which allows the retrieval of an unsatisfiable core consisting of the provided
/// assumptions passed to the initial [`Solver::satisfy_under_assumptions`]. Note that when this
/// struct is dropped (using [`Drop`]) then the [`Solver`] is reset.
#[derive(Debug)]
pub struct UnsatisfiableUnderAssumptions<'solver, 'brancher, B: Brancher> {
    pub(crate) solver: &'solver mut ConstraintSatisfactionSolver,
    pub(crate) brancher: &'brancher mut B,
}

impl<'solver, 'brancher, B: Brancher> UnsatisfiableUnderAssumptions<'solver, 'brancher, B> {
    pub fn new(
        solver: &'solver mut ConstraintSatisfactionSolver,
        brancher: &'brancher mut B,
    ) -> Self {
        UnsatisfiableUnderAssumptions { solver, brancher }
    }
}

impl<B: Brancher> Drop for UnsatisfiableUnderAssumptions<'_, '_, B> {
    fn drop(&mut self) {
        self.solver.restore_state_at_root(self.brancher)
    }
}
