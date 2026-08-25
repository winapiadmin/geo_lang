//! Sophisticated triangle + circle scenario.
//!
//! Configuration (Thales + reflection):
//! * `ABC` right-angled at `A`, `D` the foot of the altitude from `A` to the
//!   hypotenuse `BC`, `W` the midpoint of `BC` (hence the circumcenter).
//! * `R` is taken on the line `AD` beyond `D` with `RD = AD` — i.e. `R` is
//!   the reflection of `A` across the line `BC` (the user's "point on a
//!   segment at a given distance" pattern).
//!
//! Derived goals mix incidence, metric equalities and three distinct
//! concyclicity statements, including that the reflected vertex `R` lies on
//! every circle through `A`, `B`, `C`.

use geo_lang::claim::{Claim, Value};
use geo_lang::{checker, parser, prover, rules};

const SRC: &str = r#"
inp:
Triangle(A,B,C,[rightAt=A])
D=Altitude(A,BC)
W=Midpoint(BC)
R=PointOn(Line(A,D))
RD=AD
prove:
"#;

fn setup() -> (checker::FactStore, Vec<geo_lang::rules::Rule>) {
    let file = parser::parse("sophisticated.geo", SRC).expect("parse");
    let facts = checker::build_facts_from_input(&file);
    (facts, rules::rule_base())
}

fn seg(l: &str, r: &str) -> Claim {
    Claim::seg_eq(l, r)
}

fn circle(pts: &[&str]) -> Claim {
    let args: Vec<String> = pts.iter().map(|p| (*p).to_string()).collect();
    Claim::pred("OnSameCircle", &args, Value::Bool(true))
}

#[test]
fn circumcenter_equidistance_holds() {
    let (facts, rules) = setup();
    // W, the midpoint of the hypotenuse, is equidistant from all vertices.
    for (l, r) in [("WA", "WB"), ("WA", "WC"), ("WB", "WC")] {
        let g = seg(l, r);
        assert!(
            facts.contains(&g) || prover::prove(&g, &facts, &rules, 0).is_some(),
            "{l}={r} should hold"
        );
    }
}

#[test]
fn abc_is_concyclic() {
    let (facts, rules) = setup();
    let proof = prover::prove(&circle(&["A", "B", "C"]), &facts, &rules, 0)
        .expect("ABC lie on their circumcircle");
    let tree = prover::render_tree(&proof, 0, None);
    assert!(
        tree.contains("same-circle-from-equidistant")
            || tree.contains("circumcenter")
            || tree.contains("OnSameCircle"),
        "unexpected derivation:\n{tree}"
    );
}

#[test]
fn altitude_facts_hold() {
    let (facts, _) = setup();
    let perp = Claim::pred(
        "IsPerpendicular",
        &["AD".into(), "BC".into()],
        Value::Bool(true),
    );
    assert!(facts.contains(&perp), "AD is perpendicular to BC");

    let on = Claim::On("d".into(), "bc".into());
    assert!(facts.contains(&on), "foot D lies on BC");
}

#[test]
fn reflection_preserves_distance_to_w() {
    // W lies on the mirror line BC, D is the midpoint of AR and AD ⟂ BC,
    // hence the mirror preserves W's distance: WR = WA.
    let (facts, rules) = setup();
    let g = seg("WR", "WA");
    assert!(
        prover::prove(&g, &facts, &rules, 0).is_some(),
        "WR = WA should follow from the mirror argument"
    );
}

#[test]
fn d_is_midpoint_of_ar() {
    let (facts, rules) = setup();
    let g = Claim::pred(
        "IsMedian",
        &["D".into(), "AR".into()],
        Value::Bool(true),
    );
    assert!(
        prover::prove(&g, &facts, &rules, 0).is_some(),
        "D should be the midpoint of AR (reflection)"
    );
}

#[test]
fn abr_is_concyclic() {
    // R shares the circle with A and B because WR = WA = WB.
    let (facts, rules) = setup();
    let proof = prover::prove(&circle(&["A", "B", "R"]), &facts, &rules, 0)
        .expect("A, B, R concyclic");
    let rendered = format!(
        "{}{}",
        prover::render_tree(&proof, 0, None),
        prover::render_chain(&proof, None)
    );
    assert!(
        rendered.contains("same-circle-from-equidistant") || rendered.contains("OnSameCircle"),
        "expected an equidistance-based derivation, got:\n{rendered}"
    );
}

#[test]
fn arc_is_concyclic() {
    let (facts, rules) = setup();
    assert!(
        prover::prove(&circle(&["A", "R", "C"]), &facts, &rules, 0).is_some(),
        "A, R, C concyclic"
    );
}

#[test]
fn brc_is_concyclic() {
    let (facts, rules) = setup();
    assert!(
        prover::prove(&circle(&["B", "R", "C"]), &facts, &rules, 0).is_some(),
        "B, R, C concyclic"
    );
}

#[test]
fn reflected_point_lies_on_all_vertex_circles_uniformly() {
    // One-shot sweep proving every triple among {A,B,C,R} containing R.
    let (facts, rules) = setup();
    for tri in [["A", "B", "R"], ["A", "R", "C"], ["B", "R", "C"]] {
        let g = circle(&tri);
        assert!(
            prover::prove(&g, &facts, &rules, 0).is_some(),
            "{:?} should be concyclic",
            tri
        );
    }
}
