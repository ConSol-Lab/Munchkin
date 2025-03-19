#![cfg(test)]

macro_rules! encoding_tests {
    (encode_sum $encoder:ident) => {
        fn encode_sum() -> ($crate::Solver, Vec<$crate::variables::DomainId>, $crate::variables::DomainId) {
            use $crate::encodings::LinearSumEncoder;

            let mut solver = $crate::Solver::default();

            let x1 = solver.new_bounded_integer(1, 10);
            let x2 = solver.new_bounded_integer(1, 10);
            let x3 = solver.new_bounded_integer(1, 10);
            let x4 = solver.new_bounded_integer(1, 10);

            let xs = vec![x1, x2, x3, x4];

            let encoder = $crate::encodings::$encoder;
            let domain = encoder.encode(&mut solver, &xs);

            (solver, xs, domain)
        }
    };

    ($($body:tt)*) => {
        mod totalizer {
            use super::*;

            $($body)*

            encoding_tests!(encode_sum Totalizer);
        }

        mod sequential_sum {
            use super::*;

            $($body)*

            encoding_tests!(encode_sum SequentialSum);
        }
    };
}

use crate::predicate;
use crate::termination::Indefinite;

encoding_tests! {
    #[test]
    fn initial_bounds_of_output() {
        let (solver, _, out) = encode_sum();

        assert_eq!(solver.lower_bound(&out), 4);
        assert_eq!(solver.upper_bound(&out), 40);
    }

    #[test]
    fn lower_bound_is_consistent() {
        let (solver, xs, out) = encode_sum();
        let mut solver = solver.into_satisfaction_solver();

        let _ = solver.enqueue_assumption_literal(solver.get_literal(predicate![xs[0] >= 3]));
        solver.propagate_enqueued(&mut Indefinite);

        assert_eq!(solver.get_lower_bound(&out), 6);
        assert_eq!(solver.get_upper_bound(&out), 40);
    }

    #[test]
    fn lower_bound_is_consistent_2() {
        let (solver, xs, out) = encode_sum();
        let mut solver = solver.into_satisfaction_solver();

        let _ = solver.enqueue_assumption_literal(solver.get_literal(predicate![xs[0] >= 3]));
        let _ = solver.enqueue_assumption_literal(solver.get_literal(predicate![xs[1] >= 6]));
        solver.propagate_enqueued(&mut Indefinite);

        assert_eq!(solver.get_lower_bound(&out), 11);
        assert_eq!(solver.get_upper_bound(&out), 40);
    }

    #[test]
    fn upper_bound_is_consistent_1() {
        let (solver, xs, out) = encode_sum();
        let mut solver = solver.into_satisfaction_solver();

        let _ = solver.enqueue_assumption_literal(solver.get_literal(predicate![xs[0] <= 3]));
        solver.propagate_enqueued(&mut Indefinite);

        assert_eq!(solver.get_lower_bound(&out), 4);
        assert_eq!(solver.get_upper_bound(&out), 33);
    }

    #[test]
    fn upper_bound_is_consistent_2() {
        let (solver, xs, out) = encode_sum();
        let mut solver = solver.into_satisfaction_solver();

        let _ = solver.enqueue_assumption_literal(solver.get_literal(predicate![xs[4] <= 3]));
        let _ = solver.enqueue_assumption_literal(solver.get_literal(predicate![xs[3] <= 2]));
        solver.propagate_enqueued(&mut Indefinite);

        assert_eq!(solver.get_lower_bound(&out), 4);
        assert_eq!(solver.get_upper_bound(&out), 25);
    }
}
