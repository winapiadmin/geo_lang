use geo_lang::{checker, parser, prover, rules};
use rules::{match_pat, Bindings};

fn dump(label: &str, b: &[Bindings]) {
    println!("{label}: {} bindings", b.len());
    for (i, x) in b.iter().enumerate() {
        let mut pairs: Vec<_> = x.iter().collect();
        pairs.sort();
        println!("  [{i}] {:?}", pairs);
    }
}

#[test]
fn debug_rt_apex_x() {
    let src = "inp:\nTriangle(X,Y,Z,[rightAt=X])\nW=Midpoint(YZ)\nprove:\n1. OnSameCircle(X,Y,Z)=true\n";
    let file = parser::parse("test.geo", src).unwrap();
    let facts = checker::build_facts_from_input(&file);
    let rules = rules::rule_base();
    println!("facts:");
    for c in facts.all() {
        println!("  {c}");
    }

    let goal = geo_lang::claim::Claim::seg_eq("XW", "YW");
    println!("goal = {goal}");
    let r = prover::prove(&goal, &facts, &rules, 0);
    println!("SegEq(XW,YW) => {} rule={:?}", if r.is_some() { "OK" } else { "FAIL" }, r.as_ref().map(|p| p.rule.clone()));
    if let Some(p) = r {
        println!("{}", prover::render_tree(&p, 0, None));
    }

    for rule in rules.iter().filter(|r| r.id.starts_with("right-triangle-circumcenter")) {
        dump(&rule.id, &match_pat(&goal, &rule.consequent, &Bindings::new()));
    }

    let goal2 = geo_lang::claim::Claim::seg_eq("XW", "ZW");
    let r = prover::prove(&goal2, &facts, &rules, 0);
    println!("SegEq(XW,ZW) => {} rule={:?}", if r.is_some() { "OK" } else { "FAIL" }, r.as_ref().map(|p| p.rule.clone()));

    let g3 = geo_lang::claim::Claim::pred(
        "OnSameCircle",
        &["X".into(), "Y".into(), "Z".into()],
        geo_lang::claim::Value::Bool(true),
    );
    let r = prover::prove(&g3, &facts, &rules, 0);
    println!("OnSameCircle(X,Y,Z) => {} rule={:?}", if r.is_some() { "OK" } else { "FAIL" }, r.as_ref().map(|p| p.rule.clone()));

    let eq = rules.iter().find(|r| r.id == "same-circle-from-equidistant").unwrap();
    dump("goal vs same-circle-from-equidistant consequent", &match_pat(&g3, &eq.consequent, &Bindings::new()));
    println!("consequent = {:?}", eq.consequent);
}