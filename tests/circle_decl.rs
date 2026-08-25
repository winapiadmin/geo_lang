//! `Circle(center[,radius])` declarations.
//!
//! A declared circle is established by its center and — optionally — a
//! radius given as a number, as a segment length, or through a point on it.
//! Points are placed on a declared circle with `P = PointOn(K)`; internally
//! every such placement becomes an ordinary distance equality from the
//! center to the circle's radius segment, so the whole prover stack
//! (equality propagation, numeric solver, coordinate arithmetic) applies.

use geo_lang::claim::{Claim, Value};
use geo_lang::{checker, parser, prover, rules};

fn proves(src: &str, goal: &Claim) -> bool {
    let file = parser::parse("circles.geo", src).expect("parse");
    let facts = checker::build_facts_from_input(&file);
    let rules = rules::rule_base();
    facts.contains(goal) || prover::prove(goal, &facts, &rules, 0).is_some()
}

#[test]
fn numeric_radius_places_points_at_that_distance() {
    let src = r#"
inp:
O = PointOn(Line(A,B))
K = Circle(O, 3)
P = PointOn(K)
prove:
1. Distance(O,P)=3
"#;
    let goal = Claim::len_eq("OP", 3);
    assert!(proves(src, &goal), "OP must equal the declared radius 3");
}

#[test]
fn two_placed_points_are_at_equal_distance_from_the_center() {
    let src = r#"
inp:
O = PointOn(Line(A,B))
K = Circle(O, 3)
P = PointOn(K)
Q = PointOn(K)
prove:
1. OP=OQ
"#;
    assert!(proves(src, &Claim::seg_eq("OP", "OQ")));
}

#[test]
fn through_point_form_fixes_radius_and_membership() {
    // K = Circle(O, A): the radius is OA and A itself lies on K.
    let src = r#"
inp:
Triangle(A,B,C)
O=Circumcenter(ABC)
K = Circle(O, A)
Q = PointOn(K)
prove:
1. OQ=OA
"#;
    let goal = Claim::seg_eq("OQ", "OA");
    assert!(proves(src, &goal));
}

#[test]
fn circumcenter_declaration_matches_through_point() {
    // The classic identity: with O the circumcenter, Circle(O,A) passes
    // through all three vertices — placing B on it forces OB=OA.
    let src = r#"
inp:
Triangle(A,B,C,[acute=true])
O=Circumcenter(ABC)
K=Circle(O,A)
prove:
1. OnCircle(B,K)=true
"#;
    let goal = Claim::on_circle("B", "K");
    assert!(proves(src, &goal), "B lies on the circumcircle declaration");
}

#[test]
fn segment_radius_inherits_numeric_length() {
    // Radius given as a segment whose length is known numerically:
    // MP = r_K = |AB| = 6.
    let src = r#"
inp:
Triangle(A,B,C)
K = Circle(M, AB)
P = PointOn(K)
Distance(A,B)=6
prove:
1. Distance(M,P)=6
"#;
    let goal = Claim::len_eq("MP", 6);
    assert!(proves(src, &goal));
}

#[test]
fn segment_radius_equality_propagates_lengths() {
    let src = r#"
inp:
Segment(A,B)
M = PointOn(AB)
K = Circle(M, MA)
P = PointOn(K)
Distance(M,A)=4
prove:
1. Distance(M,P)=4
"#;
    let goal = Claim::len_eq("MP", 4);
    assert!(proves(src, &goal));
}

#[test]
fn on_circle_goal_with_undeclared_center_fails_cleanly() {
    // No circle named Z: the goal is simply unprovable (no crash).
    let src = r#"
inp:
Triangle(A,B,C)
prove:
1. OnCircle(A,Z)=true
"#;
    let file = parser::parse("t.geo", src).unwrap();
    let facts = checker::build_facts_from_input(&file);
    let rules = rules::rule_base();
    let goal = Claim::pred(
        "OnCircle",
        &["A".into(), "Z".into()],
        Value::Bool(true),
    );
    assert!(!facts.contains(&goal));
    let _ = prover::prove(&goal, &facts, &rules, 0);
}

#[test]
fn display_names_for_circle_predicates() {
    assert_eq!(Claim::on_circle("p1", "k1").to_string(), "OnCircle(P1,K1)");
    let center = Claim::pred(
        "IsCircleCenter",
        &["k".into(), "o".into()],
        Value::Bool(true),
    );
    assert_eq!(center.to_string(), "IsCircleCenter(K,O)");
}

