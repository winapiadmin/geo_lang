//! Coverage for the features documented in the self-documenting reference
//! `docs.geo`. The file promises "`geo_lang check docs.geo` reports proof
//! OK"; these tests pin that promise plus the individual language features
//! it describes.

use geo_lang::ast::InputStmt;
use geo_lang::claim::{Claim, Value};
use geo_lang::diag::Diagnostic;
use geo_lang::{checker, parser, prover, rules};

fn check_source(src: &str) -> Vec<Diagnostic> {
    let file = parser::parse("docs.geo", src).expect("parse");
    checker::check(&file)
}

#[test]
fn docs_geo_self_reference_checks_clean() {
    // The header of docs.geo promises exactly this.
    let src = std::fs::read_to_string("docs.geo").expect("read docs.geo");
    let diags = check_source(&src);
    let errors: Vec<_> = diags.iter().filter(|d| d.is_error()).collect();
    assert!(
        errors.is_empty(),
        "docs.geo must check without errors, got {errors:?}"
    );
}

// ---- facts documented in docs.geo ----

#[test]
fn angle_equality_input_fact_is_established() {
    // "Angle equality: Angle(ABC)=Angle(MNP)" as an inp-section fact.
    let src = r#"
inp:
Triangle(A,B,C)
D=PointOn(BC)
Angle(BAD)=Angle(DAC)
prove:
1. Angle(BAD)=Angle(DAC)
"#;
    let file = parser::parse("t.geo", src).unwrap();
    let facts = checker::build_facts_from_input(&file);
    assert!(
        file.input.iter().any(|s| matches!(s, InputStmt::AngleEq { .. })),
        "parser should produce an AngleEq statement"
    );
    assert!(
        facts.contains(&Claim::angle_eq("BAD", "DAC")),
        "angle fact established: {:?}",
        facts.all()
    );

    // ... and usable by the auto-prover.
    let rules = rules::rule_base();
    let goal = Claim::angle_eq("DAC", "BAD"); // argument order is canonical
    assert!(prover::prove(&goal, &facts, &rules, 0).is_some());
}

#[test]
fn ratio_equality_input_fact_is_established() {
    // "Ratio equality: AD/DB=AE/EC" as an inp-section fact. Claims are
    // stored canonically (both sides sorted), so BD/DC=AB/AC is recorded
    // as AB/AC = BD/CD.
    let src = r#"
inp:
Triangle(A,B,C)
D=PointOn(BC)
BD/DC=AB/AC
prove:
1. Nothing
"#;
    let file = parser::parse("t.geo", src).unwrap();
    let facts = checker::build_facts_from_input(&file);
    assert!(
        file.input.iter().any(|s| matches!(s, InputStmt::RatioEq { .. })),
        "parser should produce a RatioEq statement"
    );
    let expected = Claim::ratio_eq(
        &geo_lang::claim::RatioExpr::Quot {
            num: geo_lang::claim::RatioAtom::Seg("ab".into()),
            den: geo_lang::claim::RatioAtom::Seg("ac".into()),
        },
        &geo_lang::claim::RatioExpr::Quot {
            num: geo_lang::claim::RatioAtom::Seg("bd".into()),
            den: geo_lang::claim::RatioAtom::Seg("cd".into()),
        },
    );
    assert!(
        facts.contains(&expected),
        "ratio fact established; facts: {:?}",
        facts.all()
    );
}

#[test]
fn bare_and_distance_numeric_spellings_are_identical() {
    // docs.geo: "`AD=3` and `Distance(A,D)=3` are interchangeable".
    let short = "inp:\nSegment(A,D)\nAD=7\nprove:\n1. Nothing\n";
    let long = "inp:\nSegment(A,D)\nDistance(A,D)=7\nprove:\n1. Nothing\n";
    let fa = checker::build_facts_from_input(&parser::parse("a.geo", short).unwrap());
    let fb = checker::build_facts_from_input(&parser::parse("b.geo", long).unwrap());

    let mut la: Vec<String> = fa.all().iter().map(|c| c.to_string()).collect();
    let mut lb: Vec<String> = fb.all().iter().map(|c| c.to_string()).collect();
    la.sort();
    lb.sort();
    assert_eq!(la, lb, "both spellings must yield identical fact stores");
    assert!(
        la.iter().any(|s| s == "Distance(A,D)=7"),
        "bare form is displayed in canonical Distance spelling: {la:?}"
    );
}

// ---- goal-specific declarations ----

#[test]
fn scope_local_hides_input_facts_within_that_proof() {
    // proofProperties[N][Scope]=Local: "Local hides everything". A Local
    // block may not use premises from the enclosing scope, so a step that
    // would be fine globally reports a premise error there.
    let src = r#"
inp:
Triangle(A,B,C,[isoscelesAt=A])
D=Intersection(PerpendicularLine(A,BC),BC)
prove:
1. BD=DC
2. BD=DC
proofProperties[2][Scope]=Local
proof[1]:
(IsIsosceles(ABC)=true && IsPerpendicular(AD,BC)) -> IsMedian(D,BC)=true -> BD=DC
proof[2]:
IsMedian(D,BC)=true -> BD=DC
"#;
    let diags = check_source(src);
    assert!(
        diags.iter().any(|d| d.is_error()
            && d.message.starts_with("Premise not established: IsMedian(D,BC)")),
        "Local scope must hide the global IsMedian premise: {diags:?}"
    );
}

#[test]
fn explicit_global_scope_is_the_default() {
    // Same file without the Local declaration: both proofs check cleanly,
    // i.e. Global really is the default and nothing leaks between goals.
    let src = r#"
inp:
Triangle(A,B,C,[isoscelesAt=A])
D=Intersection(PerpendicularLine(A,BC),BC)
prove:
1. BD=DC
2. BD=DC
proofProperties[1][Scope]=Global
proof[1]:
(IsIsosceles(ABC)=true && IsPerpendicular(AD,BC)) -> IsMedian(D,BC)=true -> BD=DC
proof[2]:
IsMedian(D,BC)=true -> BD=DC
"#;
    let diags = check_source(src);
    let errors: Vec<_> = diags.iter().filter(|d| d.is_error()).collect();
    assert!(
        errors.is_empty(),
        "explicit Global must behave like the default: {errors:?}"
    );
}

#[test]
fn local_nothing_block_stays_clean_like_docs_geo() {
    // docs.geo attaches Scope=Local to a `Nothing` goal — legal precisely
    // because Nothing establishes nothing and needs no premises.
    let src = r#"
inp:
Triangle(A,B,C)
prove:
1. Nothing
proofProperties[1][Scope]=Local
proof[1]:
Nothing
"#;
    let diags = check_source(src);
    assert!(!diags.iter().any(|d| d.is_error()), "{diags:?}");
}

#[test]
fn proven_goals_reuse_across_blocks_via_global_scope() {
    // Global (default): a claim established inside proof[1] is visible to
    // later proofs and to the auto-prover for later goals.
    let src = r#"
inp:
Triangle(A,B,C,[isoscelesAt=A])
D=Intersection(PerpendicularLine(A,BC),BC)
prove:
1. BD=DC
2. IsMedian(D,BC)=true
proof[1]:
(IsIsosceles(ABC)=true && IsPerpendicular(AD,BC)) -> IsMedian(D,BC)=true -> BD=DC
"#;
    let file = parser::parse("t.geo", src).unwrap();
    let mut facts = checker::build_facts_from_input(&file);
    let _ = checker::apply_proofs(&file, &mut facts);
    let rules = rules::rule_base();

    let median = Claim::pred(
        "IsMedian",
        &["D".into(), "BC".into()],
        Value::Bool(true),
    );
    assert!(
        facts.contains(&median),
        "chain conclusion feeds later goals"
    );
}
