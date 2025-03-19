use crate::basic_types::ConflictInfo;
use crate::basic_types::PropositionalConjunction;
use crate::engine::cp::EmptyDomain;

/// The result of invoking a constraint programming propagator. The propagation can either succeed
/// or identify a conflict. The necessary conditions for the conflict must be captured in the error
/// variant, i.e. a propositional conjunction.
pub(crate) type PropagationStatusCP = Result<(), Inconsistency>;

#[derive(Debug, PartialEq, Eq)]
pub enum Inconsistency {
    EmptyDomain,
    Other(ConflictInfo),
}

impl From<EmptyDomain> for Inconsistency {
    fn from(_: EmptyDomain) -> Self {
        Inconsistency::EmptyDomain
    }
}

impl From<PropositionalConjunction> for Inconsistency {
    fn from(conjunction: PropositionalConjunction) -> Self {
        Inconsistency::Other(ConflictInfo::Explanation(conjunction))
    }
}
