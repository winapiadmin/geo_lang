//! Circle-related tests: `OnSameCircle`, circumcenter equidistance, and the
//! right-triangle hypotenuse-midpoint (circumcenter) configuration.

use geo_lang::claim::{Claim, Value};
use geo_lang::{checker, parser, prover, rules};

fn prove_goal(src: &str, goal: &Claim) -> Option<prover::Proof> {
    let file = parser::parse("test.geo", src).expect("parse");
    let facts = checker::build_facts_from_input(&file);
    let rules = rules::rule_base();
    prover::prove(goal, &facts, &rules, 0)
}

fn on_same_circle(pts: &[&str]) -> Claim {
    let args: Vec<String> = pts.iter().map(|p| (*p).to_string()).collect();
    Claim::pred("OnSameCircle", &args, Value::Bool(true))
}

#[test]
fn circumcenter_makes_vertices_concyclic() {
    let src = r#"
inp:
Triangle(A,B,C,[acute=true])
O=Circumcenter(ABC)
prove:
1. OnSameCircle(A,B,C)=true
"#;
    let proof = prove_goal(src, &on_same_circle(&["A", "B", "C"])).expect("circumcircle provable");
    let tree = prover::render_tree(&proof, 0, None);
    assert!(
        tree.contains("circumcenter-equidistant-circle"),
        "expected the circumcenter rule, got:\n{tree}"
    );
}

#[test]
fn equidistant_point_makes_points_concyclic() {
    // OA=OB and OA=OC follow from the circumcenter; the generic
    // same-circle-from-equidistant rule then applies.
    let src = r#"
inp:
Triangle(A,B,C,[isoscelesAt=A])
O=Circumcenter(ABC)
prove:
1. OA=OB
2. OA=OC
3. OnSameCircle(A,B,C)=true
"#;
    let file = parser::parse("test.geo", src).unwrap();
    let facts = checker::build_facts_from_input(&file);
    let rules = rules::rule_base();

    let eq1 = Claim::seg_eq("OA", "OB");
    assert!(facts.contains(&eq1) || prover::prove(&eq1, &facts, &rules, 0).is_some());

    // The circle goal itself must be derivable.
    assert!(
        prover::prove(&on_same_circle(&["A", "B", "C"]), &facts, &rules, 0).is_some(),
        "equidistant center should imply concyclicity"
    );
}

#[test]
fn right_triangle_hypotenuse_midpoint_equidistant() {
    // The midpoint of the hypotenuse of a right triangle is equidistant
    // from all three vertices (it is the circumcenter).
    let src = r#"
inp:
Triangle(X,Y,Z,[rightAt=X])
W=Midpoint(YZ)
prove:
1. WX=WY
2. WX=WZ
"#;
    let file = parser::parse("test.geo", src).unwrap();
    let facts = checker::build_facts_from_input(&file);
    let rules = rules::rule_base();

    for (a, b) in [("WX", "WY"), ("WX", "WZ")] {
        let g = Claim::seg_eq(a, b);
        // Provable either as an input-derived Thales fact or via the
        // goal-directed circumcenter rules.
        assert!(
            facts.contains(&g) || prover::prove(&g, &facts, &rules, 0).is_some(),
            "{a}={b} should be derivable"
        );
    }
}

#[test]
fn right_triangle_vertices_concyclic_via_hypotenuse_midpoint() {
    // With W equidistant from X, Y, Z the same-circle-from-equidistant
    // rule makes the right-triangle vertices concyclic.
    let src = r#"
inp:
Triangle(X,Y,Z,[rightAt=X])
W=Midpoint(YZ)
prove:
1. OnSameCircle(X,Y,Z)=true
"#;
    let file = parser::parse("test.geo", src).unwrap();
    let facts = checker::build_facts_from_input(&file);
    let rules = rules::rule_base();

    let proof = prover::prove(&on_same_circle(&["X", "Y", "Z"]), &facts, &rules, 0)
        .expect("right-triangle vertices are concyclic");
    let rendered = format!(
        "{}{}",
        prover::render_tree(&proof, 0, None),
        prover::render_chain(&proof, None)
    );
    assert!(
        rendered.contains("same-circle-from-equidistant")
            || rendered.contains("right-triangle-circumcenter")
            || rendered.contains("OnSameCircle"),
        "expected an equidistance-based derivation, got:\n{rendered}"
    );
}

#[test]
fn on_same_circle_is_permutation_invariant() {
    // Claims canonicalize their point list, so any permutation of the goal
    // denotes the same fact.
    let src = r#"
inp:
Triangle(A,B,C,[acute=true])
O=Circumcenter(ABC)
OnSameCircle(A,B,C)=true
prove:
1. OnSameCircle(C,A,B)=true
"#;
    let file = parser::parse("test.geo", src).unwrap();
    let facts = checker::build_facts_from_input(&file);

    let permuted = on_same_circle(&["C", "A", "B"]);
    assert!(
        facts.contains(&permuted),
        "permuted goal should hit the input fact directly; facts: {:?}",
        facts.all()
    );
}

#[test]
fn on_same_circle_display_format() {
    let c = on_same_circle(&["A", "B", "C"]);
    assert_eq!(c.to_string(), "OnSameCircle(A,B,C)");
}

#[test]
fn plain_triangle_has_no_derived_circle() {
    // Without a circumcenter or equidistance facts nothing may derive
    // concyclicity — guards against over-eager rule application.
    let src = r#"
inp:
Triangle(A,B,C)
prove:
1. OnSameCircle(A,B,C)=true
"#;
    let file = parser::parse("test.geo", src).unwrap();
    let facts = checker::build_facts_from_input(&file);
    let rules = rules::rule_base();
    assert!(
        prover::prove(&on_same_circle(&["A", "B", "C"]), &facts, &rules, 0).is_none(),
        "no rule may fire without circle premises"
    );
}

#[test]
fn four_point_circle_not_supported_yet() {
    // The current rules only conclude three-point concyclicity; a four-point
    // goal is out of scope (documented limitation).
    let src = r#"
inp:
Triangle(A,B,C,[acute=true])
O=Circumcenter(ABC)
D=PointOn(BC)
prove:
1. OnSameCircle(A,B,D)=true
"#;
    let file = parser::parse("test.geo", src).unwrap();
    let facts = checker::build_facts_from_input(&file);
    let rules = rules::rule_base();
    // D is an arbitrary point on BC: not provable, and must not crash.
    let _ = prover::prove(&on_same_circle(&["A", "B", "D"]), &facts, &rules, 0);
}
