//! Contains the representation of a unsatisfiable solution.

use crate::branching::Brancher;
use crate::engine::ConstraintSatisfactionSolver;
use crate::variables::Literal;
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

    /// Extract an unsatisfiable core in terms of the assumptions.
    ///
    /// In general, a core is a (sub)set of the constraints which together are unsatisfiable; in the
    /// case of constraint programming, this means a set of constraints which are together
    /// unsatisfiable; for example, if we have one variable `x ∈ [0, 10]` and we have the two
    /// constraints `5 * x >= 25` and `[x <= 4]` then it can be observed that these constraints can
    /// never be true at the same time.
    ///
    /// In an assumption-based solver, a core is defined as a (sub)set of assumptions which, given a
    /// set of constraints, when set together will lead to an unsatisfiable instance. For
    /// example, if we three variables `x, y, z ∈ {0, 1, 2}` and we have the constraint
    /// `all-different(x, y, z)` then the assumptions `[[x = 1], [y <= 1], [y != 0]]` would
    /// constitute an unsatisfiable core since the constraint and the assumptions can never be
    /// satisfied at the same time.
    pub fn extract_core(&mut self) -> Vec<Literal> {
        self.solver.extract_core(self.brancher)
    }
}

impl<B: Brancher> Drop for UnsatisfiableUnderAssumptions<'_, '_, B> {
    fn drop(&mut self) {
        self.solver.restore_state_at_root(self.brancher)
    }
}
