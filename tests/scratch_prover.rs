use geo_lang::{checker, parser, prover, rules};

#[test]
fn scratch_prob1() {
    let src = std::fs::read_to_string("prob1.geo").unwrap();
    let file = parser::parse(&src, &src).unwrap();
    let facts = checker::build_facts_from_input(&file);
    println!("--- facts ---");
    for f in facts.all() {
        println!("  {}", f);
    }
    let rules = rules::rule_base();
    for goal in &file.goals {
        if let Some(claim) = &goal.claim {
            for g in checker::claim_atoms(claim) {
                println!("--- goal: {} (facts? {}) ---", g, facts.contains(&g));
                match prover::prove(&g, &facts, &rules, 0) {
                    Some(p) => println!("PROVEN:\n{}", prover::render_tree(&p, 2, None)),
                    None => println!("cannot be proven"),
                }
            }
        }
    }
}