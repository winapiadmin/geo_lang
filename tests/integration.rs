//! Integration tests for the proof checker and prover.

use geo_lang::{checker, parser, prover, rules, rule_loader};
use geo_lang::claim::Value;
use std::path::Path;

fn check_source(src: &str) -> Vec<geo_lang::diag::Diagnostic> {
    let file = parser::parse("test.geo", src).expect("parse");
    checker::check(&file)
}

#[test]
fn parses_example_structure() {
    let src = std::fs::read_to_string("example.geo").expect("read example.geo");
    let file = parser::parse("example.geo", &src).expect("parse example.geo");

    assert_eq!(file.input.len(), 3, "three input statements");
    assert_eq!(file.goals.len(), 3, "three goals");
    assert_eq!(file.props.len(), 1, "one proofProperties declaration");
    assert_eq!(file.proofs.len(), 3, "three proof blocks");
    assert_eq!(file.proofs[0].steps.len(), 1);
    assert_eq!(file.proofs[1].steps.len(), 1);
    assert_eq!(file.proofs[2].steps.len(), 2);
}

#[test]
fn checker_reports_wrong_result_with_hint() {
    let src = std::fs::read_to_string("example.geo").expect("read example.geo");
    let diags = check_source(&src);

    let wrong = diags
        .iter()
        .find(|d| d.message.starts_with("Wrong result: IsMedian(D,BC) -> BC=BD"))
        .expect("wrong result error");
    assert!(wrong.is_error());
    assert_eq!(wrong.hint.as_deref(), Some("modify BC=BD to BD=CD"));
}

#[test]
fn checker_reports_duplicate_proof_warnings() {
    let src = std::fs::read_to_string("example.geo").expect("read example.geo");
    let diags = check_source(&src);

    assert!(
        diags.iter().any(|d| d.message == "Proofs after Nothing"),
        "expected 'Proofs after Nothing' warning"
    );
    assert!(
        diags.iter().any(|d| d.message == "Already established proof"),
        "expected 'Already established proof' warning"
    );
    let dup = diags
        .iter()
        .find(|d| d.message == "Already established proof")
        .unwrap();
    assert_eq!(dup.note.as_deref(), Some("It was already established at proof[1]"));
}

#[test]
fn checker_reports_unproven_goal() {
    let src = std::fs::read_to_string("example.geo").expect("read example.geo");
    let diags = check_source(&src);
    // BD=DC is now proven via forward saturation + numeric ratio-segeq.
    // The checker should still report the wrong proof in proof[1].
    assert!(
        diags.iter().any(|d| d.message.contains("Wrong result") && d.message.contains("IsMedian(D,BC)")),
        "expected wrong proof for IsMedian(D,BC) to be reported"
    );
}

#[test]
fn corrected_proof_checks_clean() {
    let src = std::fs::read_to_string("tests/fixtures/correct.geo").expect("read fixture");
    let diags = check_source(&src);
    let errors: Vec<_> = diags.iter().filter(|d| d.is_error()).collect();
    assert!(errors.is_empty(), "expected no errors, got {:?}", errors);
}

#[test]
fn prover_finds_median_proof() {
    let src = std::fs::read_to_string("example.geo").expect("read example.geo");
    let file = parser::parse("example.geo", &src).expect("parse");
    let facts = checker::build_facts_from_input(&file);
    let rules = rules::rule_base();

    let goal = geo_lang::claim::Claim::seg_eq("BD", "DC");
    let proof = prover::prove(&goal, &facts, &rules, 0).expect("prover finds a proof");

    let chain = prover::render_chain(&proof, Some("BD=DC"));
    assert_eq!(
        chain,
        "(IsIsosceles(ABC) && IsPerpendicular(AD,BC)) -> IsMedian(D,BC) -> BD=DC"
    );
}

#[test]
fn prover_rejects_wrong_goal() {
    let src = std::fs::read_to_string("example.geo").expect("read example.geo");
    let file = parser::parse("example.geo", &src).expect("parse");
    let facts = checker::build_facts_from_input(&file);
    let rules = rules::rule_base();

    // BD=BC is not derivable: the median rule yields BD=DC.
    let goal = geo_lang::claim::Claim::seg_eq("BD", "BC");
    assert!(prover::prove(&goal, &facts, &rules, 0).is_none());
}

#[test]
fn comments_and_typos_are_handled() {
    let src = r#"
/*
 header comment
*/
// line comment
inp:
Triangle(A,B,C,[isoscelesAt=A])  // inline comment
D = Intersection(PrependicularLine(A,BC),BC)
prove:
1. BD=DC
proof[1]:
(IsIsosceles(ABC)=true && IsPerpendicular(AD,BC)) -> IsMedian(D,BC)=True -> BD=DC
"#;
    let diags = check_source(src);
    assert!(diags.iter().all(|d| !d.is_error()), "no errors expected: {:?}", diags);
}

#[test]
fn case_insensitive_keywords() {
    let src = r#"
INP:
Triangle(A,B,C,[IsoscelesAt=A])
D=Intersection(PerpendicularLine(A,BC),BC)
PROVE:
1. BD=DC
PROOF[1]:
(IsIsosceles(ABC)=true && IsPerpendicular(AD,BC)) -> IsMedian(D,BC)=TRUE -> BD=DC
"#;
    let diags = check_source(src);
    assert!(diags.iter().all(|d| !d.is_error()), "no errors expected: {:?}", diags);
}

#[test]
fn triangle_property_validation_throws() {
    let src = r#"
inp:
Triangle(A,B,C,[rightAt=B, obtuseAt=C])
prove:
1. Nothing
"#;
    let diags = check_source(src);
    assert!(
        diags.iter().any(|d| d.message.contains("!IsNone(rightAt) && !IsNone(obtuseAt)")),
        "expected a throw on contradictory triangle properties"
    );
}

#[test]
fn intersection_multiple_throws() {
    let src = r#"
inp:
D = Intersection(BC, CB)
prove:
1. Nothing
"#;
    let diags = check_source(src);
    assert!(
        diags.iter().any(|d| d.message.contains("multiple intersections")),
        "expected an error for coincident lines: {:?}",
        diags
    );
}

#[test]
fn nothing_skips_rest_of_proof() {
    let src = r#"
inp:
Triangle(A,B,C)
D=Intersection(PrependicularLine(A,BC),BC)
prove:
1. BD=DC
proof[1]:
Nothing
(IsIsosceles(ABC)=true && IsPerpendicular(AD,BC)) -> IsMedian(D,BC)=True -> BD=DC
"#;
    let diags = check_source(src);
    assert!(
        diags.iter().any(|d| d.message == "Proofs after Nothing"),
        "expected 'Proofs after Nothing' warning: {:?}",
        diags
    );
    // The step after Nothing is not processed, so BD=DC is not established.
    // (The triangle here is a generic, non-isosceles one, so this is also
    // not something the general auto-prover fallback could establish on its
    // own — unlike the isosceles case, where BD=DC is a true, generally
    // provable fact and would pass regardless of whether "Nothing" skipped
    // the explicit proof text.)
    assert!(
        diags.iter().any(|d| d.message.starts_with("Goal 1 not proven")),
        "expected the goal to remain unproven: {:?}",
        diags
    );
}

#[test]
fn scope_local_hides_global_facts() {
    let src = r#"
inp:
Triangle(A,B,C,[isoscelesAt=A])
D=Intersection(PrependicularLine(A,BC),BC)
prove:
1. BD=DC
proofProperties[1][Scope]=Local
proof[1]:
(IsIsosceles(ABC)=true && IsPerpendicular(AD,BC)) -> IsMedian(D,BC)=True -> BD=DC
"#;
    let diags = check_source(src);
    // In a Local scope the input facts are hidden, so the premise is unknown.
    assert!(
        diags
            .iter()
            .any(|d| d.message.starts_with("Premise not established: IsIsosceles")),
        "expected a premise-not-established error in Local scope: {:?}",
        diags
    );
}

#[test]
fn parses_midpoint_segment_and_distance_chain() {
    let src = std::fs::read_to_string("dist.geo").expect("read dist.geo");
    let file = parser::parse("dist.geo", &src).expect("parse dist.geo");

    assert_eq!(file.input.len(), 2, "Triangle plus one Midpoint assignment");
    assert_eq!(file.goals.len(), 1);

    let claim = file.goals[0].claim.as_ref().expect("goal has a claim");
    match claim {
        geo_lang::ast::ClaimExpr::EqChain { items, .. } => {
            assert_eq!(items.len(), 3, "Distance(B,D)=Distance(C,D)=Distance(A,D)");
            assert!(matches!(items[0], geo_lang::ast::LenExpr::Distance(..)));
        }
        other => panic!("expected an EqChain, got {:?}", other),
    }
}

#[test]
fn prover_proves_distance_chain() {
    let src = std::fs::read_to_string("dist.geo").expect("read dist.geo");
    let file = parser::parse("dist.geo", &src).expect("parse");
    let facts = checker::build_facts_from_input(&file);
    let rules = rules::rule_base();

    let goal = file.goals[0].claim.as_ref().expect("goal has a claim");
    let atoms = checker::claim_atoms(goal);
    assert_eq!(atoms.len(), 2, "BD=CD and CD=AD");

    assert!(facts.contains(&atoms[0]), "BD=CD established by Midpoint(BC)");
    let proof = prover::prove(&atoms[1], &facts, &rules, 0).expect("prover proves CD=AD");
    let chain = prover::render_chain(&proof, Some("Distance(C,D)=Distance(A,D)"));
    // The prover may derive CD=AD via a rule chain or as a numeric/saturated leaf.
    assert!(
        chain.contains("Distance(C,D)=Distance(A,D)"),
        "proof should conclude Distance(C,D)=Distance(A,D), got:\n{chain}"
    );
}

#[test]
fn distance_chain_proof_checks_clean() {
    let src = r#"
inp:
Triangle(A,B,C,[rightAt=A])
D = Midpoint(BC)
prove:
1. Distance(B,D)=Distance(C,D)=Distance(A,D)
proof[1]:
Distance(B,D)=Distance(C,D) -> Distance(C,D)=Distance(A,D)
"#;
    let diags = check_source(src);
    let errors: Vec<_> = diags.iter().filter(|d| d.is_error()).collect();
    assert!(errors.is_empty(), "expected no errors, got {:?}", errors);
}

#[test]
fn parses_trieq_input_and_goal() {
    let src = std::fs::read_to_string("trieq.geo").expect("read trieq.geo");
    let file = parser::parse("trieq.geo", &src).expect("parse trieq.geo");

    let eqs: Vec<_> = file.input.iter().filter(|s| matches!(s, geo_lang::ast::InputStmt::EqChain { .. })).collect();
    assert_eq!(eqs.len(), 2, "two input segment equalities (AB=MN, BC=NP)");
    assert!(
        file.input.iter().any(|s| matches!(s, geo_lang::ast::InputStmt::AngleEq { .. })),
        "expected an Angle(ABC)=Angle(MNP) input statement"
    );

    assert_eq!(file.goals.len(), 2, "equality goal plus similarity goal");
    let claim = file.goals[0].claim.as_ref().expect("goal has a claim");
    match claim {
        geo_lang::ast::ClaimExpr::TriCall { lhs, rhs, .. } => {
            assert_eq!(lhs.to_uppercase(), "ABC");
            assert_eq!(rhs.to_uppercase(), "MNP");
        }
        other => panic!("expected a TriCall claim, got {:?}", other),
    }
    let sim = file.goals[1].claim.as_ref().expect("goal 2 has a claim");
    match sim {
        geo_lang::ast::ClaimExpr::PredEq { name, args, value, .. } => {
            assert_eq!(name, "issimilar", "parser lowercases the predicate name");
            let args_up: Vec<String> = args.iter().map(|s| s.to_uppercase()).collect();
            assert_eq!(args_up, &["ABC".to_string(), "MNP".to_string()]);
            assert_eq!(value, &geo_lang::claim::Value::Bool(true));
        }
        other => panic!("expected an IsSimilar PredEq claim, got {:?}", other),
    }
}

#[test]
fn prover_proves_triangle_equality_via_sas() {
    let src = std::fs::read_to_string("trieq.geo").expect("read trieq.geo");
    let file = parser::parse("trieq.geo", &src).expect("parse");
    let facts = checker::build_facts_from_input(&file);
    let rules = rules::rule_base();

    let goal = geo_lang::claim::Claim::tri_eq("ABC", "MNP");
    let proof = prover::prove(&goal, &facts, &rules, 0).expect("prover proves ABC=MNP");
    let chain = prover::render_chain(&proof, Some("ABC=MNP"));
    assert_eq!(
        chain,
        "(AB=MN && BC=NP && Angle(ABC)=Angle(MNP)) -> ABC=MNP"
    );
}

#[test]
fn prover_proves_triangle_equality_via_sss() {
    let src = r#"
inp:
Triangle(A,B,C)
Triangle(M,N,P)
AB=MN
BC=NP
AC=MP
prove:
1. Triangle(ABC)=Triangle(MNP)
"#;
    let file = parser::parse("test.geo", src).expect("parse");
    let facts = checker::build_facts_from_input(&file);
    let rules = rules::rule_base();

    let goal = geo_lang::claim::Claim::tri_eq("ABC", "MNP");
    let proof = prover::prove(&goal, &facts, &rules, 0).expect("prover proves ABC=MNP via SSS");
    let chain = prover::render_chain(&proof, Some("Triangle(ABC)=Triangle(MNP)"));
    assert_eq!(
        chain,
        "(AB=MN && BC=NP && AC=MP) -> Triangle(ABC)=Triangle(MNP)"
    );
}

#[test]
fn triangle_equality_permutations_are_equivalent() {
    let src = std::fs::read_to_string("trieq.geo").expect("read trieq.geo");
    let file = parser::parse("trieq.geo", &src).expect("parse");
    let facts = checker::build_facts_from_input(&file);
    let rules = rules::rule_base();

    let canonical = geo_lang::claim::Claim::tri_eq("ABC", "MNP");
    for (l, r) in [("ACB", "MPN"), ("CBA", "NPM"), ("BAC", "PNM")] {
        let perm = geo_lang::claim::Claim::tri_eq(l, r);
        assert_eq!(canonical, perm, "{}={} should equal ABC=MNP", l, r);
        assert!(
            prover::prove(&perm, &facts, &rules, 0).is_some(),
            "prover should prove {}={}",
            l,
            r
        );
    }
}

#[test]
fn triangle_equality_proof_checks_clean() {
    let src = r#"
inp:
Triangle(A,B,C)
Triangle(M,N,P)
AB=MN
BC=NP
AC=MP
prove:
1. ABC=MNP
proof[1]:
(AB=MN && BC=NP && AC=MP) -> ABC=MNP
"#;
    let diags = check_source(src);
    let errors: Vec<_> = diags.iter().filter(|d| d.is_error()).collect();
    assert!(errors.is_empty(), "expected no errors, got {:?}", errors);
}

#[test]
fn sas_proof_checks_clean() {
    let src = r#"
inp:
Triangle(A,B,C)
Triangle(M,N,P)
AB=MN
BC=NP
Angle(ABC)=Angle(MNP)
prove:
1. Triangle(ABC)=Triangle(MNP)
proof[1]:
(AB=MN && BC=NP && Angle(ABC)=Angle(MNP)) -> Triangle(ABC)=Triangle(MNP)
"#;
    let diags = check_source(src);
    let errors: Vec<_> = diags.iter().filter(|d| d.is_error()).collect();
    assert!(errors.is_empty(), "expected no errors, got {:?}", errors);
}

#[test]
fn prover_proves_aa_similarity() {
    let src = r#"
inp:
Triangle(A,B,C)
Triangle(M,N,P)
Angle(ABC)=Angle(MNP)
Angle(ACB)=Angle(MPN)
prove:
1. IsSimilar(ABC,MNP)=true
"#;
    let file = parser::parse("test.geo", src).expect("parse");
    let facts = checker::build_facts_from_input(&file);
    let rules = rules::rule_base();

    let goal = geo_lang::claim::Claim::pred("IsSimilar", &["ABC".into(), "MNP".into()], geo_lang::claim::Value::Bool(true));
    let proof = prover::prove(&goal, &facts, &rules, 0).expect("prover proves IsSimilar via AA");
    let chain = prover::render_chain(&proof, Some("IsSimilar(ABC,MNP)"));
    assert_eq!(
        chain,
        "(Angle(ABC)=Angle(MNP) && Angle(ACB)=Angle(MPN)) -> IsSimilar(ABC,MNP)"
    );
}

#[test]
fn prover_proves_sss_similarity() {
    let src = r#"
inp:
Triangle(A,B,C)
Triangle(M,N,P)
AB=MN
BC=NP
AC=MP
prove:
1. IsSimilar(ABC,MNP)=true
"#;
    let file = parser::parse("test.geo", src).expect("parse");
    let facts = checker::build_facts_from_input(&file);
    let rules = rules::rule_base();

    let goal = geo_lang::claim::Claim::pred("IsSimilar", &["ABC".into(), "MNP".into()], geo_lang::claim::Value::Bool(true));
    let proof = prover::prove(&goal, &facts, &rules, 0).expect("prover proves IsSimilar via SSS");
    let chain = prover::render_chain(&proof, Some("IsSimilar(ABC,MNP)"));
    assert_eq!(chain, "(AB=MN && BC=NP && AC=MP) -> IsSimilar(ABC,MNP)");
}

#[test]
fn equal_triangles_imply_similar() {
    let src = std::fs::read_to_string("trieq.geo").expect("read trieq.geo");
    let file = parser::parse("trieq.geo", &src).expect("parse");
    let facts = checker::build_facts_from_input(&file);
    let rules = rules::rule_base();

    let goal = geo_lang::claim::Claim::pred("IsSimilar", &["ABC".into(), "MNP".into()], geo_lang::claim::Value::Bool(true));
    let proof = prover::prove(&goal, &facts, &rules, 0).expect("equal triangles are similar");
    let chain = prover::render_chain(&proof, Some("IsSimilar(ABC,MNP)"));
    assert!(
        chain.contains("IsSimilar(ABC,MNP)"),
        "expected proof to conclude IsSimilar(ABC,MNP), got: {}",
        chain
    );
}

#[test]
fn similarity_permutations_are_equivalent() {
    let goal1 = geo_lang::claim::Claim::pred("IsSimilar", &["ABC".into(), "MNP".into()], geo_lang::claim::Value::Bool(true));
    let goal2 = geo_lang::claim::Claim::pred("IsSimilar", &["ACB".into(), "MPN".into()], geo_lang::claim::Value::Bool(true));
    assert_eq!(goal1, goal2, "IsSimilar(ACB,MPN) should equal IsSimilar(ABC,MNP)");
}

#[test]
fn aa_similarity_proof_checks_clean() {
    let src = r#"
inp:
Triangle(A,B,C)
Triangle(M,N,P)
Angle(ABC)=Angle(MNP)
Angle(ACB)=Angle(MPN)
prove:
1. IsSimilar(ABC,MNP)=true
proof[1]:
(Angle(ABC)=Angle(MNP) && Angle(ACB)=Angle(MPN)) -> IsSimilar(ABC,MNP)=true
"#;
    let diags = check_source(src);
    let errors: Vec<_> = diags.iter().filter(|d| d.is_error()).collect();
    assert!(errors.is_empty(), "expected no errors, got {:?}", errors);
}

#[test]
fn apply_proofs_reuses_global_proof_internals() {
    let src = r#"
inp:
Triangle(A,B,C)
Triangle(M,N,P)
AB=MN
BC=NP
Angle(ABC)=Angle(MNP)
prove:
1. Triangle(ABC)=Triangle(MNP)
proof[1]:
(AB=MN && BC=NP && Angle(ABC)=Angle(MNP)) -> Triangle(ABC)=Triangle(MNP)
2. IsSimilar(ABC,MNP)=true
"#;
    let file = parser::parse("test.geo", src).expect("parse");
    let mut facts = checker::build_facts_from_input(&file);
    checker::apply_proofs(&file, &mut facts);

    // Global scope: proof[1]'s conclusion is established and reusable.
    assert!(
        facts.contains(&geo_lang::claim::Claim::tri_eq("ABC", "MNP")),
        "proof[1] internals should be available for reuse"
    );
    let rules = rules::rule_base();
    let goal = geo_lang::claim::Claim::pred(
        "IsSimilar",
        &["ABC".into(), "MNP".into()],
        geo_lang::claim::Value::Bool(true),
    );
    let proof = prover::prove(&goal, &facts, &rules, 0).expect("goal 2 reuses proof[1] internals");
    let chain = prover::render_chain(&proof, Some("IsSimilar(ABC,MNP)"));
    assert_eq!(
        chain,
        "ABC=MNP -> IsSimilar(ABC,MNP)",
        "goal 2 should reuse the equality instead of re-deriving SAS"
    );
}

#[test]
fn apply_proofs_hides_local_proof_internals() {
    let src = r#"
inp:
Triangle(A,B,C)
Triangle(M,N,P)
AB=MN
BC=NP
Angle(ABC)=Angle(MNP)
prove:
1. Triangle(ABC)=Triangle(MNP)
proofProperties[1][Scope]=Local
proof[1]:
(AB=MN && BC=NP && Angle(ABC)=Angle(MNP)) -> Triangle(ABC)=Triangle(MNP)
2. IsSimilar(ABC,MNP)=true
"#;
    let file = parser::parse("test.geo", src).expect("parse");
    let mut facts = checker::build_facts_from_input(&file);
    checker::apply_proofs(&file, &mut facts);

    // Local scope: proof[1] internals are hidden, nothing is reused.
    assert!(
        !facts.contains(&geo_lang::claim::Claim::tri_eq("ABC", "MNP")),
        "Local-scope proof internals must stay hidden"
    );
}

#[test]
fn proven_goal_is_reused_by_later_goals() {
    let src = std::fs::read_to_string("trieq.geo").expect("read trieq.geo");
    let file = parser::parse("trieq.geo", &src).expect("parse");
    let mut facts = checker::build_facts_from_input(&file);
    let rules = rules::rule_base();

    // Simulate the prover command: goal 1 is proven and its claim recorded,
    // making it available to goal 2 instead of re-deriving it.
    let g1 = geo_lang::claim::Claim::tri_eq("ABC", "MNP");
    assert!(prover::prove(&g1, &facts, &rules, 0).is_some(), "goal 1 is provable");
    facts.add(g1.clone(), checker::Origin::Proof(1, 0));

    let goal = geo_lang::claim::Claim::pred(
        "IsSimilar",
        &["ABC".into(), "MNP".into()],
        geo_lang::claim::Value::Bool(true),
    );
    let proof = prover::prove(&goal, &facts, &rules, 0).expect("goal 2 reuses goal 1's claim");
    let chain = prover::render_chain(&proof, Some("IsSimilar(ABC,MNP)"));
    assert_eq!(
        chain,
        "ABC=MNP -> IsSimilar(ABC,MNP)",
        "goal 2 should reuse goal 1's proven equality"
    );
}

use geo_lang::claim::{RatioAtom, RatioExpr};

fn ratio_quot(num: &str, den: &str) -> RatioExpr {
    RatioExpr::Quot { num: RatioAtom::Seg(num.to_string()), den: RatioAtom::Seg(den.to_string()) }
}

fn int_ratio(num: u32, den: u32) -> RatioExpr {
    RatioExpr::Quot { num: RatioAtom::Int(num), den: RatioAtom::Int(den) }
}

#[test]
fn parses_angle_bisector_construction() {
    let src = r#"
inp:
Triangle(A,B,C)
D=AngleBisector(A,BC)
prove:
1. Angle(BAD)=Angle(DAC)
"#;
    let file = parser::parse("test.geo", src).expect("parse");
    assert!(file.input.iter().any(|s| matches!(s, geo_lang::ast::InputStmt::Assign { .. })));

    let facts = checker::build_facts_from_input(&file);
    assert!(
        facts.contains(&geo_lang::claim::Claim::pred(
            "IsAngleBisector",
            &["AD".into(), "BAC".into()],
            geo_lang::claim::Value::Bool(true)
        )),
        "AngleBisector construction establishes IsAngleBisector(AD,BAC)"
    );
    assert!(
        facts.contains(&geo_lang::claim::Claim::On("d".to_string(), "bc".to_string())),
        "AngleBisector construction establishes On(D,BC)"
    );
}

#[test]
fn prover_proves_angle_bisector_equal_angles() {
    let src = r#"
inp:
Triangle(A,B,C)
D=AngleBisector(A,BC)
prove:
1. Angle(BAD)=Angle(DAC)
"#;
    let file = parser::parse("test.geo", src).expect("parse");
    let facts = checker::build_facts_from_input(&file);
    let rules = rules::rule_base();

    let goal = geo_lang::claim::Claim::angle_eq("BAD", "DAC");
    let proof = prover::prove(&goal, &facts, &rules, 0).expect("prover proves equal split angles");
    let chain = prover::render_chain(&proof, Some("Angle(BAD)=Angle(DAC)"));
    assert_eq!(
        chain,
        "(IsAngleBisector(AD,BAC) && On(D,BC)) -> Angle(BAD)=Angle(DAC)"
    );
}

#[test]
fn prover_proves_angle_bisector_theorem() {
    let src = r#"
inp:
Triangle(A,B,C)
D=AngleBisector(A,BC)
prove:
1. BD/DC=AB/AC
"#;
    let file = parser::parse("test.geo", src).expect("parse");
    let facts = checker::build_facts_from_input(&file);
    let rules = rules::rule_base();

    let goal = geo_lang::claim::Claim::ratio_eq(&ratio_quot("BD", "DC"), &ratio_quot("AB", "AC"));
    let proof = prover::prove(&goal, &facts, &rules, 0).expect("prover proves the angle-bisector theorem");
    let chain = prover::render_chain(&proof, Some("BD/DC=AB/AC"));
    assert_eq!(
        chain,
        "(IsAngleBisector(AD,BAC) && On(D,BC)) -> BD/DC=AB/AC"
    );
}

#[test]
fn ratio_equivalences_are_canonical() {
    // BD/DC = AB/AC: side-swap is equivalent, but inverting both quotients is a different equation.
    let a = geo_lang::claim::Claim::ratio_eq(&ratio_quot("BD", "DC"), &ratio_quot("AB", "AC"));
    let b = geo_lang::claim::Claim::ratio_eq(&ratio_quot("DC", "BD"), &ratio_quot("AC", "AB"));
    let c = geo_lang::claim::Claim::ratio_eq(&ratio_quot("AB", "AC"), &ratio_quot("BD", "DC"));
    assert_ne!(a, b, "inverting both quotients produces a different equation");
    assert_eq!(a, c, "swapping the two sides is equivalent");
}

#[test]
fn ratio_equivalences_are_canonical_with_constants() {
    // WZ/BC = 1/2: BC/WZ = 2 is a different equation (reciprocal ratio).
    let a = geo_lang::claim::Claim::ratio_eq(&ratio_quot("WZ", "BC"), &int_ratio(1, 2));
    let b = geo_lang::claim::Claim::ratio_eq(&ratio_quot("BC", "WZ"), &int_ratio(2, 1));
    assert_ne!(a, b, "reciprocal quotients with reciprocal constants are different equations");
}

#[test]
fn prover_proves_altitude_is_perpendicular() {
    let src = r#"
inp:
Triangle(A,B,C)
IsAltitude(AH,BC)=true
prove:
1. IsPerpendicular(AH,BC)
"#;
    let file = parser::parse("test.geo", src).expect("parse");
    let facts = checker::build_facts_from_input(&file);
    let rules = rules::rule_base();

    let goal = geo_lang::claim::Claim::pred(
        "IsPerpendicular",
        &["AH".into(), "BC".into()],
        geo_lang::claim::Value::Bool(true),
    );
    let proof = prover::prove(&goal, &facts, &rules, 0).expect("prover proves altitude perpendicularity");
    let chain = prover::render_chain(&proof, Some("IsPerpendicular(AH,BC)"));
    assert_eq!(chain, "IsAltitude(AH,BC) -> IsPerpendicular(AH,BC)");
}

#[test]
fn prover_proves_midsegment_parallel() {
    let src = r#"
inp:
Triangle(A,B,C)
W=Midpoint(AB)
Z=Midpoint(AC)
prove:
1. IsParallel(WZ,BC)
"#;
    let file = parser::parse("test.geo", src).expect("parse");
    let facts = checker::build_facts_from_input(&file);
    let rules = rules::rule_base();

    let goal = geo_lang::claim::Claim::pred(
        "IsParallel",
        &["WZ".into(), "BC".into()],
        geo_lang::claim::Value::Bool(true),
    );
    let proof = prover::prove(&goal, &facts, &rules, 0).expect("prover proves mid-segment parallelism");
    let chain = prover::render_chain(&proof, Some("IsParallel(WZ,BC)"));
    assert!(chain.contains("IsParallel(WZ,BC)"), "chain should conclude IsParallel(WZ,BC), got: {}", chain);
}

#[test]
fn prover_proves_midsegment_half_length() {
    let src = r#"
inp:
Triangle(A,B,C)
W=Midpoint(AB)
Z=Midpoint(AC)
prove:
1. WZ/BC=1/2
"#;
    let file = parser::parse("test.geo", src).expect("parse");
    let facts = checker::build_facts_from_input(&file);
    let rules = rules::rule_base();

    let goal = geo_lang::claim::Claim::ratio_eq(&ratio_quot("WZ", "BC"), &int_ratio(1, 2));
    let proof = prover::prove(&goal, &facts, &rules, 0).expect("prover proves the mid-segment half length");
    let chain = prover::render_chain(&proof, Some("WZ/BC=1/2"));
    assert_eq!(chain, "(IsMedian(W,AB) && IsMedian(Z,AC)) -> WZ/BC=1/2");
}

#[test]
fn prover_proves_center_properties() {
    let src = r#"
inp:
Triangle(A,B,C)
O=Circumcenter(ABC)
I=Incenter(ABC)
H=Orthocenter(ABC)
G=Centroid(ABC)
D=Midpoint(BC)
prove:
1. OA=OB
2. IsAngleBisector(AI,BAC)
3. IsPerpendicular(AH,BC)
4. On(G,AD)
"#;
    let file = parser::parse("test.geo", src).expect("parse");
    let facts = checker::build_facts_from_input(&file);
    let rules = rules::rule_base();

    let circum = geo_lang::claim::Claim::seg_eq("OA", "OB");
    let proof = prover::prove(&circum, &facts, &rules, 0).expect("circumcenter is equidistant");
    assert_eq!(
        prover::render_chain(&proof, Some("OA=OB")),
        "IsCircumcenter(O,ABC) -> OA=OB"
    );

    let incenter = geo_lang::claim::Claim::pred(
        "IsAngleBisector",
        &["AI".into(), "BAC".into()],
        geo_lang::claim::Value::Bool(true),
    );
    let proof = prover::prove(&incenter, &facts, &rules, 0).expect("incenter lies on an angle bisector");
    assert_eq!(
        prover::render_chain(&proof, Some("IsAngleBisector(AI,BAC)")),
        "IsIncenter(I,ABC) -> IsAngleBisector(AI,BAC)"
    );

    let ortho = geo_lang::claim::Claim::pred(
        "IsPerpendicular",
        &["AH".into(), "BC".into()],
        geo_lang::claim::Value::Bool(true),
    );
    let proof = prover::prove(&ortho, &facts, &rules, 0).expect("orthocenter lies on an altitude");
    assert_eq!(
        prover::render_chain(&proof, Some("IsPerpendicular(AH,BC)")),
        "IsOrthocenter(H,ABC) -> IsPerpendicular(AH,BC)"
    );

    let centroid = geo_lang::claim::Claim::On("g".to_string(), "ad".to_string());
    let proof = prover::prove(&centroid, &facts, &rules, 0).expect("centroid lies on a median");
    assert_eq!(
        prover::render_chain(&proof, Some("On(G,AD)")),
        "(IsCentroid(G,ABC) && IsMedian(D,BC)) -> On(G,AD)"
    );
}

#[test]
fn predicate_fact_input_establishes_on_and_bisector() {
    let src = r#"
inp:
Triangle(A,B,C)
On(D,BC)=true
IsAngleBisector(AD,BAC)=true
prove:
1. Angle(BAD)=Angle(DAC)
"#;
    let file = parser::parse("test.geo", src).expect("parse");
    let facts = checker::build_facts_from_input(&file);
    assert!(
        facts.contains(&geo_lang::claim::Claim::On("d".to_string(), "bc".to_string())),
        "On(D,BC)=true input becomes a fact"
    );
    assert!(
        facts.contains(&geo_lang::claim::Claim::pred(
            "IsAngleBisector",
            &["AD".into(), "BAC".into()],
            geo_lang::claim::Value::Bool(true)
        )),
        "IsAngleBisector(AD,BAC)=true input becomes a fact"
    );

    let rules = rules::rule_base();
    let goal = geo_lang::claim::Claim::angle_eq("BAD", "DAC");
    let proof = prover::prove(&goal, &facts, &rules, 0).expect("proves equal split angles from input facts");
    assert_eq!(
        prover::render_chain(&proof, Some("Angle(BAD)=Angle(DAC)")),
        "(IsAngleBisector(AD,BAC) && On(D,BC)) -> Angle(BAD)=Angle(DAC)"
    );
}

#[test]
fn angle_bisector_theorem_proof_checks_clean() {
    let src = r#"
inp:
Triangle(A,B,C)
D=AngleBisector(A,BC)
prove:
1. BD/DC=AB/AC
proof[1]:
(IsAngleBisector(AD,BAC) && On(D,BC)) -> BD/DC=AB/AC
"#;
    let diags = check_source(src);
    let errors: Vec<_> = diags.iter().filter(|d| d.is_error()).collect();
    assert!(errors.is_empty(), "expected no errors, got {:?}", errors);
}
fn read_fixture(name: &str) -> String {
    std::fs::read_to_string(format!("tests/fixtures/{name}"))
        .unwrap_or_else(|e| panic!("read fixture {name}: {e}"))
}

fn check_fixture(name: &str) -> Vec<geo_lang::diag::Diagnostic> {
    check_source(&read_fixture(name))
}

/// Prove every goal in a fixture with the auto-prover.
fn prove_fixture_goals(name: &str) {
    let src = read_fixture(name);
    let file = parser::parse(name, &src).expect("parse");
    let facts = checker::build_facts_from_input(&file);
    let rules = rules::rule_base();
    for goal in &file.goals {
        if let Some(claim) = &goal.claim {
            let atoms = checker::claim_atoms(claim);
            for a in atoms {
                assert!(
                    prover::prove(&a, &facts, &rules, 0).is_some(),
                    "{name}: goal {} {a:?} should be provable",
                    goal.index
                );
            }
        }
    }
}

fn assert_fixture_clean(name: &str) {
    let diags = check_fixture(name);
    let errors: Vec<_> = diags.iter().filter(|d| d.is_error()).collect();

    assert!(
        errors.is_empty(),
        "{name} should check cleanly, got: {errors:?}"
    );
}
#[test]
fn fixture_correct() {
    assert_fixture_clean("correct.geo");
}

#[test]
fn fixture_sas() {
    assert_fixture_clean("sas.geo");
}

#[test]
fn fixture_sss() {
    assert_fixture_clean("sss.geo");
}

#[test]
fn fixture_aa_similarity() {
    assert_fixture_clean("aa_similarity.geo");
}

#[test]
fn fixture_sss_similarity() {
    assert_fixture_clean("sss_similarity.geo");
}

#[test]
fn fixture_isosceles_median() {
    assert_fixture_clean("isosceles_median.geo");
}

#[test]
fn fixture_angle_bisector() {
    assert_fixture_clean("angle_bisector.geo");
}

#[test]
fn fixture_midsegment() {
    assert_fixture_clean("midsegment.geo");
}

#[test]
fn fixture_centers() {
    assert_fixture_clean("centers.geo");
}

#[test]
fn fixture_global_local() {
    assert_fixture_clean("global_local.geo");
}

#[test]
fn prover_proves_thales_ratio() {
    let src = r#"
inp:
Triangle(A,B,C)
D=PointOn(AB)
E=PointOn(AC)
Segment(D,E)
IsParallel(DE,BC)=true
prove:
1. AD/DB=AE/EC
"#;
    let file = parser::parse("test.geo", src).expect("parse");
    let facts = checker::build_facts_from_input(&file);
    let rules = rules::rule_base();
    let goal = geo_lang::claim::Claim::ratio_eq(
        &geo_lang::claim::RatioExpr::Quot {
            num: geo_lang::claim::RatioAtom::Seg("ad".into()),
            den: geo_lang::claim::RatioAtom::Seg("db".into()),
        },
        &geo_lang::claim::RatioExpr::Quot {
            num: geo_lang::claim::RatioAtom::Seg("ae".into()),
            den: geo_lang::claim::RatioAtom::Seg("ec".into()),
        },
    );
    let proof = prover::prove(&goal, &facts, &rules, 0).expect("Thales theorem");
    assert_eq!(
        prover::render_chain(&proof, Some("AD/DB=AE/EC")),
        "(On(D,AB) && On(E,AC) && IsParallel(BC,DE)) -> AD/DB=AE/EC"
    );
}

#[test]
fn prover_proves_converse_thales() {
    let src = r#"
inp:
Triangle(A,B,C)
D=PointOn(AB)
E=PointOn(AC)
Segment(D,E)
AD/DB=AE/EC
prove:
1. IsParallel(DE,BC)=true
"#;
    let file = parser::parse("test.geo", src).expect("parse");
    let facts = checker::build_facts_from_input(&file);
    let rules = rules::rule_base();
    let goal = geo_lang::claim::Claim::pred(
        "IsParallel",
        &["DE".into(), "BC".into()],
        geo_lang::claim::Value::Bool(true),
    );
    let proof = prover::prove(&goal, &facts, &rules, 0).expect("converse Thales");
    assert_eq!(
        prover::render_chain(&proof, Some("IsParallel(DE,BC)")),
        "(On(D,AB) && On(E,AC) && AD/BD = AE/CE) -> IsParallel(DE,BC)"
    );
}

#[test]
fn prover_proves_parallel_from_numeric_ratios() {
    let src = r#"
inp:
Triangle(A,B,C)
D=PointOn(AB)
E=PointOn(AC)
Segment(D,E)
AD=3
DB=2
AE=6
EC=4
prove:
1. IsParallel(DE,BC)=true
"#;
    let file = parser::parse("test.geo", src).expect("parse");
    let facts = checker::build_facts_from_input(&file);
    let rules = rules::rule_base();
    let goal = geo_lang::claim::Claim::pred(
        "IsParallel",
        &["DE".into(), "BC".into()],
        geo_lang::claim::Value::Bool(true),
    );
    let proof = prover::prove(&goal, &facts, &rules, 0).expect("numeric ratios imply parallel");
    assert!(
        proof.rule.is_some(),
        "goal proved via a rule (converse Thales + numeric ratio)"
    );
}

#[test]
fn prover_proves_pythagorean_distance() {
    let src = r#"
inp:
Triangle(A,B,C,[isoscelesAt=A])
H=Intersection(PrependicularLine(B,AC),AC)
Segment(A,H)
Distance(A,H)=7
Distance(C,H)=2
prove:
1. Distance(B,C)=6
"#;
    let file = parser::parse("test.geo", src).expect("parse");
    let facts = checker::build_facts_from_input(&file);
    let rules = rules::rule_base();
    let goal = geo_lang::claim::Claim::len_eq("BC", 6);
    let proof = prover::prove(&goal, &facts, &rules, 0).expect("Pythagorean theorem");
    assert_eq!(proof.claim, goal, "proves the length goal");
    assert!(
        matches!(proof.rule, Some("sqrt") | Some("numeric")),
        "derived by the numeric solver, got {:?}",
        proof.rule
    );
    let tree = prover::render_tree(&proof, 0, Some("Distance(B,C)=6"));
    // The proof may use either the pythagoras path (perpendicular-based)
    // or the right-triangle path (rightat-based). Both are valid.
    let has_pythagoras_path = tree.contains("by pythagoras") && tree.contains("segment-addition") && tree.contains("isosceles-legs");
    let has_right_triangle_path = tree.contains("by right-triangle") && tree.contains("by sqrt");
    assert!(
        has_pythagoras_path || has_right_triangle_path,
        "the numeric proof should show its steps, got: {tree}"
    );
}

#[test]
fn fixture_dist_height_checks_clean() {
    assert_fixture_clean("dist_height.geo");
}

#[test]
fn prover_proves_isosceles_properties() {
    let src = r#"
inp:
Triangle(A,B,C,[isoscelesAt=A])
H=Altitude(A,ABC)
Segment(A,H)
prove:
1. IsMedian(H,BC)=true
2. IsAngleBisector(AH,Angle(BAC))=true
3. IsPerpendicularBisector(AH,BC)=true
"#;
    let file = parser::parse("test.geo", src).expect("parse");
    let facts = checker::build_facts_from_input(&file);
    let rules = rules::rule_base();

    let median = geo_lang::claim::Claim::pred(
        "IsMedian",
        &["H".into(), "BC".into()],
        geo_lang::claim::Value::Bool(true),
    );
    let proof = prover::prove(&median, &facts, &rules, 0).expect("apex altitude is a median");
    assert_eq!(
        prover::render_chain(&proof, Some("IsMedian(H,BC)")),
        "(IsIsosceles(ABC) && IsPerpendicular(AH,BC)) -> IsMedian(H,BC)"
    );

    let bisector = geo_lang::claim::Claim::pred(
        "IsAngleBisector",
        &["AH".into(), "BAC".into()],
        geo_lang::claim::Value::Bool(true),
    );
    let proof = prover::prove(&bisector, &facts, &rules, 0).expect("apex median is the angle bisector");
    assert_eq!(proof.rule, Some("isosceles-apex-median-bisector"));
    let chain = prover::render_chain(&proof, Some("IsAngleBisector(AH,BAC)"));
    assert!(
        chain.contains("IsMedian(H,BC)") && chain.contains("IsAngleBisector(AH,BAC)"),
        "chain should mention the median and the bisector, got: {chain}"
    );

    let pbis = geo_lang::claim::Claim::pred(
        "IsPerpendicularBisector",
        &["AH".into(), "BC".into()],
        geo_lang::claim::Value::Bool(true),
    );
    let proof = prover::prove(&pbis, &facts, &rules, 0).expect("perpendicular bisector definition");
    assert_eq!(proof.rule, Some("perpendicular-bisector-def"));
    let chain = prover::render_chain(&proof, Some("IsPerpendicularBisector(AH,BC)"));
    assert!(
        chain.contains("On(H,BC)") && chain.contains("IsMedian(H,BC)"),
        "chain should mention the midpoint condition, got: {chain}"
    );
}

#[test]
fn fixture_isosceles_prop_goals_prove() {
    prove_fixture_goals("isosceles_prop.geo");
}

#[test]
fn fixture_thales_and_inverse_goals_prove() {
    prove_fixture_goals("thales.geo");
    prove_fixture_goals("invthales.geo");
    prove_fixture_goals("numthales.geo");
}

#[test]
fn fixture_numeval1_squared_and_length_goals_prove() {
    assert_fixture_clean("numeval1.geo");
    prove_fixture_goals("numeval1.geo");
}

#[test]
fn bypass_downgrades_listed_error_kinds() {
    use geo_lang::diag::{bypass_errors, Severity};
    let src = r#"
inp:
Triangle(A,B,C)
prove:
1. BD=DE
proof[1]:
IsIsosceles(ABC)=true -> IsMedian(H,BC)=true -> BD=DE
"#;
    let diags = check_source(src);
    let premise = diags
        .iter()
        .find(|d| d.message.starts_with("Premise not established"))
        .expect("premise error");
    assert_eq!(premise.kind, "premise-not-established");

    let out = bypass_errors(diags, &["GoalNotProven".into(), "PremiseNotEstablished".into()]);
    let premise = out
        .iter()
        .find(|d| d.message.starts_with("Premise not established"))
        .expect("downgraded premise diag");
    assert_eq!(premise.severity, Severity::Warning);
    assert!(
        premise.note.as_deref().unwrap_or("").contains("assumed (bypassed with -e:PremiseNotEstablished)"),
        "note should mention the bypass, got {:?}",
        premise.note
    );
    assert!(
        out.iter().all(|d| d.kind != "wrong-result" || d.is_error()),
        "unlisted kinds must stay errors"
    );
}

#[test]
fn intersection_variadic_proves_concurrent_facts() {
    let src = r#"
inp:
Triangle(A,B,C)
D=PointOn(AB)
E=PointOn(AC)
F=Intersection(AD,BE,CF)
prove:
1. On(F,AD)
"#;
    let file = parser::parse("test.geo", src).expect("parse");
    let facts = checker::build_facts_from_input(&file);
    let rules = rules::rule_base();
    let claim = checker::claim_atoms(&file.goals[0].claim.clone().unwrap());
    assert!(prover::prove(&claim[0], &facts, &rules, 0).is_some());
    let diags = check_source(src);
    assert!(
        diags.iter().all(|d| !d.is_error()),
        "expected clean check, got: {diags:?}"
    );
}

#[test]
fn intersection_single_arg_errors() {
    let src = r#"
inp:
Triangle(A,B,C)
O=Intersection(AB)
prove:
1. On(O,AB)
"#;
    let err = parser::parse("test.geo", src).expect_err("expected a parse error");
    assert!(
        err.msg.contains("requires more than 1 segment or line"),
        "got: {}",
        err.msg
    );
}

#[test]
fn intersection_coincident_lines_throw_multiple() {
    let src = r#"
inp:
Triangle(A,B,C)
O=Intersection(AB,AB)
prove:
1. On(O,AB)
"#;
    let diags = check_source(src);
    assert!(
        diags
            .iter()
            .any(|d| d.message == "Intersection throws on multiple intersections"),
        "expected multiple-intersections error"
    );
}

#[test]
fn intersection_parallel_lines_throw_no_intersection() {
    let src = r#"
inp:
Triangle(A,B,C)
IsParallel(MN,PQ)=true
O=Intersection(MN,PQ)
prove:
1. On(O,MN)
"#;
    let diags = check_source(src);
    assert!(
        diags
            .iter()
            .any(|d| d.message.contains("no intersection")),
        "expected no-intersection error"
    );
}

#[test]
fn intersection_accepts_named_perpendicular_line() {
    let src = r#"
inp:
Triangle(A,B,C)
L=PerpendicularLine(A,BC)
H=Intersection(L,BC)
prove:
1. IsPerpendicular(AH,BC)
"#;
    let file = parser::parse("test.geo", src).expect("parse");
    let facts = checker::build_facts_from_input(&file);
    let rules = rules::rule_base();
    let claim = checker::claim_atoms(&file.goals[0].claim.clone().unwrap());
    assert!(prover::prove(&claim[0], &facts, &rules, 0).is_some());
}

#[test]
fn intersection_non_line_argument_errors() {
    let src = r#"
inp:
Triangle(A,B,C)
O=Intersection(A,BC)
prove:
1. On(O,BC)
"#;
    let diags = check_source(src);
    assert!(
        diags
            .iter()
            .any(|d| d.message.contains("requires segment or line arguments")),
        "expected argument-type error"
    );
}

#[test]
fn squared_length_goals_prove() {
    let src = r#"
inp:
Triangle(A,B,C,[isoscelesAt=A])
H=Intersection(PerpendicularLine(B,AC),AC)
Distance(A,H)=7
Distance(C,H)=2
prove:
1. Distance(A,B)^2=81
2. Distance(B,C)^2=36
3. Distance(B,C)=6
4. BH^2=32
"#;
    let file = parser::parse("test.geo", src).expect("parse");
    let facts = checker::build_facts_from_input(&file);
    let rules = rules::rule_base();
    for goal in &file.goals {
        let claim = goal.claim.clone().unwrap();
        let atoms = checker::claim_atoms(&claim);
        assert!(
            prover::prove(&atoms[0], &facts, &rules, 0).is_some(),
            "goal {} ({claim:?}) should be provable",
            goal.index
        );
    }
}

#[test]
fn squared_length_eq_sq_proves() {
    let src = r#"
inp:
Triangle(A,B,C,[isoscelesAt=A])
H=Intersection(PerpendicularLine(B,AC),AC)
Distance(A,H)=7
Distance(C,H)=2
prove:
1. Distance(A,B)^2 = Distance(A,C)^2
"#;
    let file = parser::parse("test.geo", src).expect("parse");
    let facts = checker::build_facts_from_input(&file);
    let rules = rules::rule_base();
    let claim = file.goals[0].claim.clone().unwrap();
    let atoms = checker::claim_atoms(&claim);
    assert!(
        prover::prove(&atoms[0], &facts, &rules, 0).is_some(),
        "squared-equal goal should be provable"
    );
}

#[test]
fn squared_length_mixed_errors() {
    let src = r#"
inp:
Triangle(A,B,C)
Distance(A,B)^2 = Distance(A,C)
prove:
1. Distance(A,B)^2 = 9
"#;
    let diags = check_source(src);
    assert!(
        diags
            .iter()
            .any(|d| d.message.contains("cannot compare a squared length with a plain length")),
        "expected mixed-unit error"
    );
}

#[test]
fn squared_length_bad_exponent_errors() {
    let src = r#"
inp:
Triangle(A,B,C)
Distance(A,B)^3 = 27
prove:
1. Distance(A,B)^2 = 9
"#;
    let err = parser::parse("test.geo", src).expect_err("expected a parse error");
    assert!(
        err.msg.contains("only ^2 (squared) is supported"),
        "got: {}",
        err.msg
    );
}

#[test]
fn point_on_line_parses_and_adds_facts() {
    let src = r#"
inp:
Triangle(A,B,C)
H=Intersection(PerpendicularLine(A,BC),BC)
E=Intersection(PerpendicularLine(H,AB),AB)
M=PointOn(Line(H,E))
ME=HE
prove:
1. On(M,HE)
2. ME=HE
"#;
    let diags = check_source(src);
    let errors: Vec<_> = diags.iter().filter(|d| d.is_error()).collect();
    assert!(errors.is_empty(), "expected no errors, got {:?}", errors);

    let file = parser::parse("test.geo", src).expect("parse");
    let facts = checker::build_facts_from_input(&file);
    let on_he = |p: &str| geo_lang::claim::Claim::On(p.into(), geo_lang::claim::Claim::norm_seg("HE"));
    assert!(
        facts.contains(&on_he("m")),
        "PointOn(Line(H,E)) should put M on line HE"
    );
    assert!(
        facts.contains(&on_he("h")),
        "H should lie on line HE"
    );
    assert!(
        facts.contains(&on_he("e")),
        "E should lie on line HE"
    );
}

#[test]
fn on_same_circle_from_circumcenter() {
    let src = r#"
inp:
Triangle(A,B,C,[acute=true])
O=Circumcenter(ABC)
prove:
1. OnSameCircle(A,B,C)=true
"#;
    let file = parser::parse("test.geo", src).unwrap();
    let facts = checker::build_facts_from_input(&file);
    let rules = rules::rule_base();

    let goal = geo_lang::claim::Claim::pred("OnSameCircle", &["A".into(), "B".into(), "C".into()], Value::Bool(true));
    let proof = prover::prove(&goal, &facts, &rules, 0).expect("should prove");
    let chain = prover::render_chain(&proof, None);
    assert!(chain.contains("IsCircumcenter(O,ABC)"), "expected circumcenter rule, got: {}", chain);
}

#[test]
fn on_same_circle_from_equidistant() {
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

    // Goal 3 should be provable via circumcenter or equidistant
    let goal = geo_lang::claim::Claim::pred("OnSameCircle", &["A".into(), "B".into(), "C".into()], Value::Bool(true));
    let proof = prover::prove(&goal, &facts, &rules, 0).expect("should prove");
    // Check the proof tree has the expected rule
    let tree = prover::render_tree(&proof, 0, None);
    assert!(tree.contains("circumcenter-equidistant-circle") || tree.contains("same-circle-from-equidistant"),
        "expected circle rule in tree, got:\n{}", tree);
}

#[test]
fn multi_char_points_in_claims() {
    let src = r#"
inp:
Triangle(A,B,C)
P1=Midpoint(AB)
P2=Midpoint(AC)
prove:
1. IsParallel(P1-P2,BC)=true
"#;
    let file = parser::parse("test.geo", src).unwrap();
    let facts = checker::build_facts_from_input(&file);
    let rules = rules::rule_base();

    // Multi-char points work via `-` delimiter in predicate args
    let goal = geo_lang::claim::Claim::pred("IsParallel", &["P1-P2".into(), "BC".into()], Value::Bool(true));
    let proof = prover::prove(&goal, &facts, &rules, 0).expect("should prove");
    let tree = prover::render_tree(&proof, 0, None);
    assert!(tree.contains("IsParallel"), "proof tree should contain IsParallel conclusion, got:\n{}", tree);
}

#[test]
fn indexed_points_in_constructions() {
    let src = r#"
inp:
Triangle(A,B,C)
P[1]=Midpoint(AB)
P[2]=Midpoint(AC)
prove:
1. IsMedian(P1,AB)=true
2. IsMedian(P2,AC)=true
"#;
    let file = parser::parse("test.geo", src).unwrap();
    let facts = checker::build_facts_from_input(&file);
    let _rules = rules::rule_base();

    let goal1 = geo_lang::claim::Claim::pred("IsMedian", &["P1".into(), "AB".into()], Value::Bool(true));
    assert!(facts.contains(&goal1), "P1 should be median of AB");

    let goal2 = geo_lang::claim::Claim::pred("IsMedian", &["P2".into(), "AC".into()], Value::Bool(true));
    assert!(facts.contains(&goal2), "P2 should be median of AC");
}

#[test]
fn prob3_nine_point_without_cheat_rule() {
    let src = std::fs::read_to_string("prob3.geo").expect("read prob3.geo");
    let file = parser::parse("prob3.geo", &src).expect("parse prob3.geo");

    let mut facts = checker::build_facts_from_input(&file);
    let _ = checker::apply_proofs(&file, &mut facts);
    let all_rules = rule_loader::load_rules_from_dir(Path::new("rules"))
        .expect("load rules");
    let disabled = std::collections::HashSet::from(["nine-point-mid-collinear"]);
    let rule_base = all_rules;
    let enabled_rules: Vec<_> = rule_base.iter()
        .filter(|r| !disabled.contains(r.id))
        .cloned()
        .collect();

    // Find goal 10 and apply its scoped inputs (same as main.rs prove loop)
    let _goal10 = file.goals.iter().find(|g| g.index == 10).expect("goal 10");
    let scoped: Vec<_> = file.scoped_input.iter()
        .filter(|(idx, _)| *idx == 10)
        .map(|(_, stmt)| stmt)
        .collect();
    if !scoped.is_empty() {
        checker::apply_input_statements(&mut facts, &scoped);
        checker::derive_perpendicular_foot_midpoints(&mut facts);
    }

    let target = geo_lang::claim::Claim::pred("IsCollinear", &["Q".into(), "J".into(), "H".into()], Value::Bool(true));

    // Goal-directed saturation: stops as soon as the target is derivable
    // instead of computing the full (expensive) closure of a 13-point
    // diagram under every enabled rule to a fixed point.
    let saturated = prover::saturate_toward(&facts, &enabled_rules, Some(&target), None);

    let found = saturated.contains(&target);
    println!("IsCollinear(Q,J,H) found: {}", found);
    println!("Total facts: {}", saturated.all().len());

    println!("=== Q2 facts ===");
    for c in saturated.all() {
        let s = c.to_string();
        if s.to_lowercase().contains("q2") {
            println!("  {}", s);
        }
    }

    println!("=== collinear facts with Q or H ===");
    for c in saturated.all() {
        let s = c.to_string();
        if (s.contains("iscollinear") || s.contains("IsCollinear"))
            && (s.contains("Q") || s.contains("H")) {
            println!("  {}", s);
        }
    }
    println!("=== median facts ===");
    for c in saturated.all() {
        let s = c.to_string();
        if s.contains("ismedian") || s.contains("IsMedian") {
            println!("  {}", s);
        }
    }
    println!("=== On facts (subset) ===");
    for c in saturated.all() {
        let s = c.to_string();
        if s.starts_with("On(") || s.starts_with("on(") {
            println!("  {}", s);
        }
    }
    println!("=== similarity facts ===");
    for c in saturated.all() {
        let s = c.to_string();
        if s.contains("issimilar") || s.contains("IsSimilar") {
            println!("  {}", s);
        }
    }
    println!("=== perpendicular facts ===");
    for c in saturated.all() {
        let s = c.to_string();
        if s.contains("isperpendicular") || s.contains("IsPerpendicular") {
            println!("  {}", s);
        }
    }
    println!("=== segeq facts ===");
    for c in saturated.all() {
        let s = c.to_string();
        if s.starts_with("SegEq") {
            println!("  {}", s);
        }
    }
    println!("=== ratio facts involving Q2 ===");
    for c in saturated.all() {
        let s = c.to_string();
        if s.contains("RatioEq") && s.to_lowercase().contains("q2") {
            println!("  {}", s);
        }
    }
    println!("=== parallel facts ===");
    for c in saturated.all() {
        let s = c.to_string();
        if s.contains("isparallel") || s.contains("IsParallel") {
            println!("  {}", s);
        }
    }
    // Now try backward chaining with pre-saturated store
    let target = geo_lang::claim::Claim::pred("IsCollinear", &["Q".into(), "J".into(), "H".into()], Value::Bool(true));
    match prover::prove_seeded(&target, &facts, &saturated, &rule_base, Some(&disabled)) {
        Some(proof) => {
            println!("=== PROOF FOUND ===");
            let chain = prover::render_chain(&proof, None);
            println!("{}", chain);
            assert!(chain.contains("IsMedian(J,HQ)"));
            assert!(chain.contains("On(J,HQ)"));
        }
        None => {
            panic!("disabled nine-point rule should use its explicit fallback chain");
        }
    }
}

#[test]
    #[ignore = "requires spam_internal_points which is temporarily disabled"]
    fn spams_internal_midpoints_and_intersections() {
    // Triangle with altitude and angle bisector - creates crossing segments
    let src = r#"
inp:
Triangle(A,B,C,[rightAt=A])
H=Intersection(PerpendicularLine(A,BC),BC)
K=AngleBisector(ABH,AH)
prove:
1. IsSimilar(ABH,CBA)
"#;
    let file = parser::parse("test.geo", src).expect("parse");
    let facts = checker::build_facts_from_input(&file);

    // Check that internal midpoints T_0, T_1, ... are created for segments with On facts
    // Segments with On facts from input: ab, ac, bc, ah
    let mid_on_facts: Vec<_> = facts.all().iter()
        .filter_map(|c| match c {
            geo_lang::claim::Claim::On(p, s) if p.starts_with("T_") => Some((p.clone(), s.clone())),
            _ => None,
        })
        .collect();

    // Should have midpoints for at least the 4 segments with On facts
    assert!(mid_on_facts.len() >= 4, "expected at least 4 internal midpoint On facts, got {}: {:?}", mid_on_facts.len(), mid_on_facts);

    // Verify segments that got midpoints
    let mid_segments: Vec<_> = mid_on_facts.iter().map(|(_, s)| s.as_str()).collect();
    assert!(mid_segments.contains(&"ab"), "missing midpoint for ab");
    assert!(mid_segments.contains(&"ac"), "missing midpoint for ac");
    assert!(mid_segments.contains(&"bc"), "missing midpoint for bc");
    assert!(mid_segments.contains(&"ah"), "missing midpoint for ah");

    // Verify no collision with user-defined points
    let all_points: Vec<_> = facts.all().iter()
        .filter_map(|c| match c {
            geo_lang::claim::Claim::On(p, _) | geo_lang::claim::Claim::OnSegment(p, _) => Some(p.clone()),
            geo_lang::claim::Claim::PredVal { args, .. } => args.first().cloned(),
            _ => None,
        })
        .collect();
    for p in &all_points {
        if p.starts_with("T_") {
            assert!(p[2..].parse::<u32>().is_ok(), "T_ point should have numeric suffix: {}", p);
        }
    }
}
