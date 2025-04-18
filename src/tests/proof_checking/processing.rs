#![cfg(test)]

use drcp_format::reader::ProofReader;
use drcp_format::steps::Conclusion;
use drcp_format::writer::ProofWriter;
use drcp_format::Format;
use drcp_format::LiteralDefinitions;

use crate::model::Constraint;
use crate::model::Model;
use crate::proof;
use crate::proof::processing::Processor;
use crate::proof::ProofLiterals;
use crate::variables::Literal;

fn example_processor() -> Processor {
    let mut model = Model::default();

    let x = model.new_interval_variable("x", 0, 1);
    let y = model.new_interval_variable("y", 0, 2);
    let z = model.new_interval_variable("z", 0, 1);

    // c1
    model.add_constraint(Constraint::LinearLessEqual {
        terms: vec![x.scaled(-2), y.scaled(-1), z.scaled(-2)],
        rhs: -2,
    });
    // c2
    model.add_constraint(Constraint::LinearLessEqual {
        terms: vec![x.scaled(-2), y.scaled(-1), z.scaled(2)],
        rhs: 0,
    });
    // c3
    model.add_constraint(Constraint::LinearLessEqual {
        terms: vec![x.scaled(-2), y.scaled(1), z.scaled(-2)],
        rhs: 0,
    });
    // c4
    model.add_constraint(Constraint::LinearLessEqual {
        terms: vec![x.scaled(-2), y.scaled(1), z.scaled(2)],
        rhs: 2,
    });
    // c5
    model.add_constraint(Constraint::LinearLessEqual {
        terms: vec![x.scaled(2), y.scaled(-1), z.scaled(-2)],
        rhs: -2,
    });
    // c6
    model.add_constraint(Constraint::LinearLessEqual {
        terms: vec![x.scaled(2), y.scaled(-1), z.scaled(2)],
        rhs: 0,
    });

    Processor::from(model.clone())
}

#[test]
fn test_trim() {
    let mut processor = example_processor();

    // Internally we expect only >= atomic constraints, so we put everything into that form
    let literals = r#"
    1 [x >= 1]
    2 [y >= 2]
    3 [y >= 1]
    4 [z >= 1]
    "#;

    let definitions = LiteralDefinitions::<String>::parse(literals.as_bytes()).unwrap();

    // The first number is the ID, then the numbers after indicate the premise literals, minus
    // indicating it is negated and the numbers mapping to the literals defined above
    let scaffold = r#"
        n 1 -1 2
        n 2 -3 4
        n 3 -1 -2
        n 4 -1
        n 5
        c UNSAT
    "#;

    let proof = ProofReader::new(
        scaffold.as_bytes(),
        processor.initialise_proof_literals(definitions),
    );

    let (nogoods, conclusion) = proof::processing::trim(&mut processor, proof).unwrap();

    assert!(matches!(conclusion, Conclusion::<Literal>::Unsatisfiable));

    assert_eq!(nogoods.len(), 3);
    let nogood_0 = &nogoods[0];
    assert_eq!(nogood_0.len(), 2);
    assert!(nogood_0.contains(&Literal::u32_to_literal(7)));
    assert!(nogood_0.contains(&Literal::u32_to_literal(2)));
    let nogood_1 = &nogoods[1];
    assert!(nogood_1.contains(&Literal::u32_to_literal(6)));
    assert!(nogood_1.contains(&Literal::u32_to_literal(2)));
    let nogood_2 = &nogoods[2];
    assert!(nogood_2.contains(&Literal::u32_to_literal(2)));
}

#[test]
fn test_inference_introduction() {
    let mut processor = example_processor();

    // Note that this is exactly the expected output of trim for the example scaffold in the other
    // test
    let literal_2 = Literal::u32_to_literal(2);
    let literal_6 = Literal::u32_to_literal(6);
    let literal_7 = Literal::u32_to_literal(7);
    let nogoods = vec![
        vec![literal_2.clone(), literal_7.clone()],
        vec![literal_6.clone(), literal_2.clone()],
        vec![literal_2.clone()],
    ];

    let mut buf = Vec::new();
    {
        let mut writer = ProofWriter::new(Format::Text, &mut buf, ProofLiterals::default());
        proof::processing::introduce_inferences(&mut processor, nogoods, &mut writer).unwrap();
    }
    let proof_text = String::from_utf8(buf).unwrap();
    let expected_proof = r#"
        i 1 -2 3 0 1 c:3 l:linear
        i 2 3 1 0 2 c:4 l:linear
        n 3 -2 3 0 1 2
        i 4 4 -3 0 1 c:5 l:linear
        i 5 -3 1 0 -4 c:6 l:linear
        n 6 -3 -2 0 4 5
        n 7 -2 0 3 6
        i 8 2 4 0 1 c:5 l:linear
        i 9 4 1 0 -2 c:6 l:linear
        n 10 0 7 8 9
    "#;

    // We do the trimming because the format doesn't care about whitespace and so we are robust
    // to any small implementation changes that change the whitespace
    let lines_proof = proof_text.trim().lines();
    let lines_expected = expected_proof.trim().lines();
    assert_eq!(lines_proof.clone().count(), lines_expected.clone().count());
    for (proof_l, expected_l) in lines_proof.into_iter().zip(lines_expected.into_iter()) {
        assert_superset(proof_l, expected_l)
    }
}

fn assert_superset(proof: &str, expected: &str) {
    let proof = proof.trim();
    let expected = expected.trim();

    let type_proof = expected.chars().next().unwrap();
    let type_expected = expected.chars().next().unwrap();
    assert!(type_proof == type_expected);
    if type_expected == 'i' {
        return;
    }
    let mut split_proof = proof[2..].split("c").next().unwrap().split(" 0");
    let mut split_expected = expected[2..].split("c").next().unwrap().split(" 0");

    let proof_lhs = split_proof
        .next()
        .unwrap()
        .split(" ")
        .filter(|element| !element.trim().is_empty())
        .map(|element| {
            element
                .parse::<i32>()
                .expect("Expected {element} to be parseable to int")
        })
        .collect::<Vec<_>>();
    let expected_lhs = split_expected
        .next()
        .unwrap()
        .split(" ")
        .filter(|element| !element.trim().is_empty())
        .map(|element| {
            element
                .parse::<i32>()
                .expect("Expected {element} to be parseable to int")
        })
        .collect::<Vec<_>>();

    for element in expected_lhs {
        assert!(proof_lhs.contains(&element));
    }

    let proof_rhs = split_proof.next();
    let expected_rhs = split_expected.next();
    match (proof_rhs, expected_rhs) {
        (Some(proof_rhs), Some(expected_rhs)) => {
            if proof_rhs != expected_rhs {
                panic!("Hints should be identical!");
            }
        }
        (x, y) => panic!("Your hints: {x:?} but expected: {y:?}"),
    }
}
