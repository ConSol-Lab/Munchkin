use super::TerminationCondition;

/// A [`TerminationCondition`] which triggers when the specified conflict budget has been exceeded.
#[derive(Clone, Copy, Debug)]
pub struct ConflictBudget {
    budget: usize,
    encountered: usize,
}

impl ConflictBudget {
    /// Give the solver a time budget, starting now.
    #[allow(unused, reason = "Might be used in the assignment")]
    pub fn with_budget(budget: usize) -> Self {
        Self {
            budget,
            encountered: 0,
        }
    }
}

impl TerminationCondition for ConflictBudget {
    fn should_stop(&mut self) -> bool {
        self.encountered >= self.budget
    }

    fn encountered_conflict(&mut self) {
        self.encountered += 1
    }
}
