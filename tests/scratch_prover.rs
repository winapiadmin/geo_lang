use geo_lang::{checker, parser, prover, rules};
use std::time::Instant;

#[test]
fn scratch_stress() {
    let src = std::fs::read_to_string("stress_parallel_perp.geo").unwrap();
    let file = parser::parse("stress_parallel_perp.geo", &src).unwrap();
    let rules = rules::rule_base();
    let mut facts = checker::build_facts_from_input(&file);
    let _ = checker::apply_proofs(&file, &mut facts);
    let mut saturated = prover::forward_saturate(&facts, &rules);

    // Prove goals 1..28, feeding each result back into the saturated store
    // (mirrors the CLI flow), then stress the cross-perpendicular goal 29.
    for goal in &file.goals {
        if goal.index > 28 {
            break;
        }
        if let Some(claim) = &goal.claim {
            for g in checker::claim_atoms(claim) {
                if !saturated.contains(&g) {
                    let _ = prover::prove_seeded(&g, &facts, &saturated, &rules);
                }
                facts.add(g.clone(), checker::Origin::Proof(goal.index, 0));
                saturated.add(g.clone(), checker::Origin::Proof(goal.index, 0));
            }
        }
    }
    println!("facts after 28 goals: {}", saturated.all().len());

    let goal = geo_lang::claim::Claim::pred(
        "IsPerpendicular",
        &["FM".into(), "DR".into()],
        geo_lang::claim::Value::Bool(true),
    );
    let t = Instant::now();
    let r = prover::prove_seeded(&goal, &facts, &saturated, &rules);
    println!(
        "goal29 => {} in {:?}, rule={:?}",
        if r.is_some() { "OK" } else { "FAIL" },
        t.elapsed(),
        r.as_ref().map(|p| p.rule)
    );
    assert!(r.is_some(), "goal29 should be provable");
}
