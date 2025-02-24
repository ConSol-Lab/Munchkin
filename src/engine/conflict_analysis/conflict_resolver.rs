use super::ConflictAnalysisContext;
use crate::variables::Literal;

pub(crate) trait ConflictResolver {
    /// Resolves the current conflict.
    ///
    /// If the [`ConflictResolver`] learns a nogood then it should be returned (and [`None`]
    /// otherwrise).
    fn resolve_conflict(&mut self, context: &mut ConflictAnalysisContext) -> Option<LearnedNogood>;

    /// After creating the learned nogood in [`ConflictResolver::resolve_conflict`], this method
    /// should put the solver in the "correct" state (e.g. by backtracking using
    /// [`ConflictAnalysisContext::backtrack`]).
    fn process(
        &mut self,
        learned_nogood: Option<LearnedNogood>,
        context: &mut ConflictAnalysisContext,
    ) -> Result<(), ()>;
}

/// A structure which stores a learned nogood
///
/// There are two assumptions:
/// - The asserting literal (i.e. the literal of the current decision level) is placed at the `0`th
///   index of [`LearnedNogood::literals`].
/// - A literal from the second-highest decision level is placed at the `1`st index of
///   [`LearnedNogood::literals`].
///
/// A [`LearnedNogood`] can be created using either [`LearnedNogood::new`] or, in the case of a
/// unit learned nogood, using [`LearnedNogood::unit_learned_nogood`].
#[derive(Clone, Debug, Default)]
pub(crate) struct LearnedNogood {
    pub(crate) literals: Vec<Literal>,
    pub(crate) backjump_level: usize,
}

#[allow(unused, reason = "will be used in the assignments")]
impl LearnedNogood {
    pub(crate) fn new(literals: impl IntoIterator<Item = Literal>, backjump_level: usize) -> Self {
        Self {
            literals: literals.into_iter().collect::<Vec<_>>(),
            backjump_level,
        }
    }

    pub(crate) fn unit_learned_nogood(literal: Literal) -> Self {
        Self {
            literals: vec![literal],
            backjump_level: 0,
        }
    }

    pub(crate) fn to_clause(&self) -> Vec<Literal> {
        self.literals
            .iter()
            .copied()
            .map(|literal| !literal)
            .collect()
    }
}
