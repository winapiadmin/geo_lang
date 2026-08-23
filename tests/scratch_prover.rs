use geo_lang::{checker, parser, prover, rules};
use std::time::Instant;

fn reordered(rules: &[rules::Rule]) -> Vec<rules::Rule> {
    let ids = [
        "parallel-transitivity",
        "perp-with-parallel",
        "trapezoid-midline",
        "midsegment-parallel",
        "midpoint-collinear",
        "midsegment-half-length",
        "midsegment-midpoint-on-median",
        "altitude-is-perpendicular",
    ];
    let mut out: Vec<rules::Rule> = Vec::new();
    for id in ids {
        if let Some(r) = rules.iter().find(|r| r.id == id) {
            out.push(r.clone());
        }
    }
    for r in rules.iter().filter(|r| !ids.contains(&r.id)) {
        out.push(r.clone());
    }
    out
}

#[test]
fn scratch_stress() {
    let src = std::fs::read_to_string("stress_parallel_perp.geo").unwrap();
    let file = parser::parse("stress_parallel_perp.geo", &src).unwrap();
    let rules = reordered(&rules::rule_base());
    let mut sound = checker::build_facts_from_input(&file);
    let _ = checker::apply_proofs(&file, &mut sound);
    let _saturated = prover::forward_saturate(&sound, &rules);

    for goal in &file.goals {
        if goal.index > 28 { break; }
        if let Some(claim) = &goal.claim {
            for g in checker::claim_atoms(claim) {
                if !sound.contains(&g) {
                    let _ = prover::prove(&g, &sound, &rules, 0);
                }
                sound.add(g.clone(), checker::Origin::Proof(goal.index, 0));
            }
        }
    }
    println!("facts after 28 goals: {}", sound.all().len());

    let goal = geo_lang::claim::Claim::pred(
        "IsPerpendicular",
        &["FM".into(), "DR".into()],
        geo_lang::claim::Value::Bool(true),
    );
    let t = Instant::now();
    let r = prover::prove(&goal, &sound, &rules, 0);
    println!("goal29 (reordered) => {} in {:?}, rule={:?}", if r.is_some() {"OK"} else {"FAIL"}, t.elapsed(), r.as_ref().map(|p| p.rule));
}