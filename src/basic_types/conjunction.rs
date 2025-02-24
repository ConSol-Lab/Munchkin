use crate::variables::Literal;

pub(crate) struct Conjunction {
    #[allow(unused, reason = "Will be used in the assignment")]
    pub(crate) literals: Vec<Literal>,
}

impl From<Vec<Literal>> for Conjunction {
    fn from(value: Vec<Literal>) -> Self {
        Self { literals: value }
    }
}
