use super::MinimisationContext;
use super::Minimiser;
use crate::engine::conflict_analysis::LearnedNogood;

pub(crate) struct RecursiveMinimiser {
    // TODO
}

impl Default for RecursiveMinimiser {
    #[allow(clippy::derivable_impls, reason = "Will be implemented")]
    fn default() -> Self {
        Self {}
    }
}

impl Minimiser for RecursiveMinimiser {
    fn minimise(&mut self, _context: MinimisationContext, _learned_nogood: &mut LearnedNogood) {
        todo!()
    }
}
