use super::Clause;
use crate::basic_types::ClauseReference;
use crate::engine::variables::Literal;
use crate::munchkin_assert_advanced;
use crate::munchkin_assert_moderate;
use crate::munchkin_assert_simple;

#[derive(Default, Debug)]
pub(crate) struct ClauseAllocator {
    allocated_clauses: Vec<Clause>,
    deleted_clause_references: Vec<ClauseReference>,
}

impl ClauseAllocator {
    pub(crate) fn create_clause(
        &mut self,
        literals: Vec<Literal>,
        is_learned: bool,
    ) -> ClauseReference {
        // todo - add assert to ensure that the clause is as we expect, e.g., no duplicate literals.
        // Normally preprocess_clause would get rid of this. Perhaps could move the responsibility
        // to the clause manager, and have an unchecked version for learned clauses
        munchkin_assert_simple!(literals.len() >= 2);

        if self.deleted_clause_references.is_empty() {
            // create a new clause reference, unseen before
            let clause_reference = ClauseReference::create_allocated_clause_reference(
                self.allocated_clauses.len() as u32 + 1,
            ); // we keep clause reference id zero as the null value, never to be allocated at that
               // position

            self.allocated_clauses
                .push(Clause::new(literals, is_learned));

            clause_reference
        } else {
            // reuse a clause reference from the deleted clause pool
            let clause_reference = self.deleted_clause_references.pop().unwrap();
            self.allocated_clauses[clause_reference.get_code() as usize - 1] =
                Clause::new(literals, is_learned);

            clause_reference
        }
    }

    pub(crate) fn get_mutable_clause(&mut self, clause_reference: ClauseReference) -> &mut Clause {
        &mut self.allocated_clauses[clause_reference.get_code() as usize - 1]
        //-1 since clause ids go from one, and not zero
    }

    pub(crate) fn get_clause(&self, clause_reference: ClauseReference) -> &Clause {
        &self.allocated_clauses[clause_reference.get_code() as usize - 1]
        //-1 since clause ids go from one, and not zero
    }

    pub(crate) fn delete_clause(&mut self, clause_reference: ClauseReference) {
        munchkin_assert_moderate!(
            clause_reference.get_code() - 1 < self.allocated_clauses.len() as u32
        );
        // note that in the current implementation 'deleting' a clause simply labels its clause
        // reference as available  so next time a new clause is created, it can freely take
        // the value of a previous deleted clause  this may change if we change the clause
        // allocation mechanism as usual in SAT solvers
        munchkin_assert_moderate!(
            !self.get_clause(clause_reference).is_deleted(),
            "Cannot delete an already deleted clause."
        );
        munchkin_assert_advanced!(
            !self.deleted_clause_references.contains(&clause_reference),
            "Somehow the id of the deleted clause is already present in the internal data structure,
             meaning we are deleting the clause twice, unexpected."
        );

        self.get_mutable_clause(clause_reference).mark_deleted();
        self.deleted_clause_references.push(clause_reference);
    }
}

impl std::ops::Index<ClauseReference> for ClauseAllocator {
    type Output = Clause;
    fn index(&self, clause_reference: ClauseReference) -> &Clause {
        self.get_clause(clause_reference)
    }
}

impl std::ops::IndexMut<ClauseReference> for ClauseAllocator {
    fn index_mut(&mut self, clause_reference: ClauseReference) -> &mut Clause {
        self.get_mutable_clause(clause_reference)
    }
}

impl std::fmt::Display for ClauseAllocator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let clauses_string = &self
            .allocated_clauses
            .iter()
            .fold(String::new(), |acc, clause| format!("{acc}{clause}\n"));

        let num_clauses = self.allocated_clauses.len();
        write!(f, "Num clauses: {num_clauses}\n{clauses_string}")
    }
}
