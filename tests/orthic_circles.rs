//! Orthic-circle bouquet: five distinct circles in one triangle.
//!
//! Configuration: acute triangle `ABC`, orthocenter `H`, altitude feet
//! `D ∈ BC`, `E ∈ CA`, `F ∈ AB`.
//!
//! Circles proved to coexist:
//! 1. **Circumcircle** `⊙ABC` (center `O`);
//! 2. **⊙BDH** — right-angled at `D` (`DB ⊥ DH`), center `U = Midpoint(BH)`;
//! 3. **⊙CEH** — right-angled at `E`, center `V = Midpoint(CH)`;
//! 4. **⊙AFH** — right-angled at `F`, center `T = Midpoint(AH)`;
//! 5. **Diameter-BC circle** — `∠BEC = ∠BFC = 90°`, so `E` and `F` lie on the
//!    circle with diameter `BC`, center `N = Midpoint(BC)`; in particular the
//!    two altitude feet `E, F` are concyclic with `B` and `C`.
//!
//! The right-angle premises are supplied as input predicate facts
//! (`IsRight(...)=true`, `RightAt(...)=<vertex>`), exercising the parser's
//! `Value::Point` path alongside the geometric constructions.

use geo_lang::claim::{Claim, Value};
use geo_lang::{checker, parser, prover, rules};

const SRC: &str = r#"
inp:
Triangle(A,B,C,[acute=true])
H=Orthocenter(ABC)
D=Altitude(A,BC)
E=Altitude(B,AC)
F=Altitude(C,AB)
O=Circumcenter(ABC)
N=Midpoint(B,C)
U=Midpoint(B,H)
V=Midpoint(C,H)
T=Midpoint(A,H)

IsRight(BDH)=true
RightAt(BDH)=D
IsRight(CEH)=true
RightAt(CEH)=E
IsRight(AFH)=true
RightAt(AFH)=F
IsRight(BEC)=true
RightAt(BEC)=E
IsRight(BFC)=true
RightAt(BFC)=F

prove:
"#;

fn setup() -> (checker::FactStore, Vec<geo_lang::rules::Rule>) {
    let file = parser::parse("orthic.geo", SRC).expect("parse");
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

fn proves(goal: &Claim, facts: &checker::FactStore, rules: &[geo_lang::rules::Rule]) -> bool {
    facts.contains(goal) || prover::prove(goal, facts, rules, 0).is_some()
}

// ---- circle 1: circumcircle ----

#[test]
fn circumcenter_equidistance() {
    let (facts, rules) = setup();
    for (l, r) in [("OA", "OB"), ("OB", "OC"), ("OA", "OC")] {
        assert!(proves(&seg(l, r), &facts, &rules), "{l}={r}");
    }
}

#[test]
fn circumcircle_abc() {
    let (facts, rules) = setup();
    assert!(proves(&circle(&["A", "B", "C"]), &facts, &rules));
}

// ---- circles 2–4: orthic sub-circles through H ----

#[test]
fn subcircle_bdh_equidistance() {
    let (facts, rules) = setup();
    for (l, r) in [("UB", "UD"), ("UD", "UH"), ("UB", "UH")] {
        assert!(proves(&seg(l, r), &facts, &rules), "{l}={r}");
    }
}

#[test]
fn subcircle_ceh_equidistance() {
    let (facts, rules) = setup();
    for (l, r) in [("VC", "VE"), ("VE", "VH"), ("VC", "VH")] {
        assert!(proves(&seg(l, r), &facts, &rules), "{l}={r}");
    }
}

#[test]
fn subcircle_afh_equidistance() {
    let (facts, rules) = setup();
    for (l, r) in [("TA", "TF"), ("TF", "TH"), ("TA", "TH")] {
        assert!(proves(&seg(l, r), &facts, &rules), "{l}={r}");
    }
}

#[test]
fn subcircles_concyclic_triples() {
    let (facts, rules) = setup();
    for tri in [["B", "D", "H"], ["C", "E", "H"], ["A", "F", "H"]] {
        assert!(proves(&circle(&tri), &facts, &rules), "{:?} concyclic", tri);
    }
}

// ---- circle 5: diameter-BC circle through the feet E, F ----

#[test]
fn diameter_center_equidistance() {
    let (facts, rules) = setup();
    // N, the midpoint of BC, is equidistant from B, C and both feet.
    for (l, r) in [("NB", "NC"), ("NB", "NE"), ("NB", "NF"), ("NE", "NF")] {
        assert!(proves(&seg(l, r), &facts, &rules), "{l}={r}");
    }
}

#[test]
fn feet_lie_on_diameter_circle() {
    let (facts, rules) = setup();
    for tri in [["B", "C", "E"], ["B", "C", "F"], ["B", "E", "F"], ["C", "E", "F"]] {
        assert!(proves(&circle(&tri), &facts, &rules), "{:?} concyclic", tri);
    }
}

#[test]
fn e_and_f_are_symmetric_on_the_diameter_circle() {
    // The two feet together with either endpoint span the same circle.
    let (facts, rules) = setup();
    for tri in [["E", "F", "B"], ["E", "F", "C"]] {
        assert!(proves(&circle(&tri), &facts, &rules), "{:?} concyclic", tri);
    }
}

// ---- structural cross-checks ----

#[test]
fn altitude_incidence_and_perpendicularity() {
    let (facts, _) = setup();
    for p in [("d", "bc"), ("e", "ac"), ("f", "ab")] {
        assert!(facts.contains(&Claim::On(p.0.into(), p.1.into())));
    }
    for (x, base) in [("AD", "BC"), ("BE", "AC"), ("CF", "AB")] {
        let g = Claim::pred(
            "IsPerpendicular",
            &[x.into(), base.into()],
            Value::Bool(true),
        );
        assert!(facts.contains(&g), "{x} perpendicular to {base}");
    }
}

#[test]
fn degenerate_collinear_triple_is_not_circular() {
    // A, D, H are collinear; nothing may "derive" a circle through them —
    // guards against over-eager application of the equidistance rules.
    let (facts, rules) = setup();
    assert!(!proves(&circle(&["A", "D", "H"]), &facts, &rules));
}
