use crate::variables::Literal;
use crate::Solver;

pub(super) struct CoreMinimiser;

impl CoreMinimiser {
    /// Minimises the provided `core` using deletion-based core minimisation
    #[allow(unused, reason = "Will be used in the assignment")]
    pub(super) fn minimise_core(_core: &mut Vec<Literal>, _solver: &mut Solver) {
        todo!()
    }
}
