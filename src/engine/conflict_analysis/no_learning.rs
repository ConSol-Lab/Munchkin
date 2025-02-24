use super::ConflictAnalysisContext;
use super::ConflictResolver;
use super::LearnedNogood;

#[derive(Debug, Copy, Clone)]
pub(crate) struct NoLearning;

impl ConflictResolver for NoLearning {
    fn resolve_conflict(
        &mut self,
        _context: &mut ConflictAnalysisContext,
    ) -> Option<LearnedNogood> {
        // In the case of no learning, this method does not do anything
        None
    }

    fn process(
        &mut self,
        _learned_nogood: Option<LearnedNogood>,
        context: &mut ConflictAnalysisContext,
    ) -> Result<(), ()> {
        let last_decision = context.get_last_decision();

        context.backtrack(context.get_decision_level() - 1);
        context.enqueue_propagated_literal(!last_decision);
        Ok(())
    }
}
