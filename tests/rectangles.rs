//! `IsRectangle(A,B,C,D)=true` declarations.
//!
//! Declaring a rectangle (vertices in order) derives the side structure:
//! adjacent sides perpendicular, opposite sides parallel. With numeric side
//! lengths the Pythagorean machinery then proves the classical rectangle
//! theorem — both diagonals are equal.

use geo_lang::claim::{Claim, Value};
use geo_lang::{checker, parser, prover, rules};

const SRC: &str = r#"
inp:
IsRectangle(A,B,C,D)=true
prove:
"#;

fn setup() -> (checker::FactStore, Vec<geo_lang::rules::Rule>) {
    let file = parser::parse("rect.geo", SRC).expect("parse");
    let facts = checker::build_facts_from_input(&file);
    (facts, rules::rule_base())
}

fn proves(goal: &Claim, facts: &checker::FactStore, rules: &[geo_lang::rules::Rule]) -> bool {
    facts.contains(goal) || prover::prove(goal, facts, rules, 0).is_some()
}

#[test]
fn adjacent_sides_perpendicular() {
    let (facts, rules) = setup();
    for pair in [("AB", "BC"), ("BC", "CD"), ("CD", "AD"), ("AD", "AB")] {
        let g = Claim::pred(
            "IsPerpendicular",
            &[pair.0.into(), pair.1.into()],
            Value::Bool(true),
        );
        assert!(proves(&g, &facts, &rules), "{} perpendicular {}", pair.0, pair.1);
    }
}

#[test]
fn opposite_sides_parallel() {
    let (facts, rules) = setup();
    for pair in [("AB", "CD"), ("BC", "DA")] {
        let g = Claim::pred(
            "IsParallel",
            &[pair.0.into(), pair.1.into()],
            Value::Bool(true),
        );
        assert!(proves(&g, &facts, &rules), "{} parallel {}", pair.0, pair.1);
    }
}

#[test]
fn parallel_survives_side_swapping() {
    // Claims canonicalize their arguments, so BC||DA must also answer DA||BC.
    let (facts, rules) = setup();
    let g = Claim::pred(
        "IsParallel",
        &["DA".into(), "BC".into()],
        Value::Bool(true),
    );
    assert!(proves(&g, &facts, &rules));
}

#[test]
fn diagonals_are_equal() {
    // The classical rectangle theorem: both diagonals are hypotenuses of
    // congruent 3-4-5 right triangles cut off by the corners.
    let src = r#"
inp:
Triangle(A,B,C)
Segment(C,D)
IsRectangle(A,B,C,D)=true
Distance(A,B)=3
Distance(B,C)=4
Distance(C,D)=3
prove:
1. AC=BD
"#;
    let file = parser::parse("r.geo", src).expect("parse");
    let facts = checker::build_facts_from_input(&file);
    let rules = rules::rule_base();
    let goal = Claim::seg_eq("AC", "BD");
    assert!(
        prover::prove(&goal, &facts, &rules, 0).is_some(),
        "diagonals of a rectangle are equal"
    );
}

#[test]
fn display_name() {
    let g = Claim::pred(
        "IsRectangle",
        &["A".into(), "B".into(), "C".into(), "D".into()],
        Value::Bool(true),
    );
    assert_eq!(g.to_string(), "IsRectangle(A,B,C,D)");
}
