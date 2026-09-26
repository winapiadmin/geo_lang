use geo_lang::claim::Claim;
use geo_lang::{checker, parser, prover, rules};

const SRC: &str = r#"
inp:
Triangle(A,B,C,[rightAt=A])
H=Intersection(PerpendicularLine(A,BC), BC)
K=AngleBisector(ABH,AH)
prove:
1. KA*AB=KH*CB
"#;

fn main() {
    let file = parser::parse("prob12.geo", SRC).expect("parse");
    let facts = checker::build_facts_from_input(&file);
    let rule_list = rules::rule_base();
    let goal3 = Claim::ratio_eq(
        &geo_lang::claim::RatioExpr::Quot {
            num: geo_lang::claim::RatioAtom::Seg("ka".to_string()),
            den: geo_lang::claim::RatioAtom::Seg("kh".to_string()),
        },
        &geo_lang::claim::RatioExpr::Quot {
            num: geo_lang::claim::RatioAtom::Seg("cb".to_string()),
            den: geo_lang::claim::RatioAtom::Seg("ab".to_string()),
        },
    );
    println!("goal3: {}", goal3);

    // Check if angle-bisector-theorem rule loads
    let ab_rules: Vec<_> = rule_list
        .iter()
        .filter(|r| r.id.contains("angle-bisector") || r.id.contains("bisector"))
        .collect();
    for r in &ab_rules {
        println!("\nrule: {}", r.id);
        println!("  antecedents: {:?}", r.antecedents);
        println!("  consequent: {:?}", r.consequent);
    }

    let sat = prover::saturate_toward(&facts, &rule_list, Some(&goal3), None);

    println!("\n--- All facts ({} total) ---", sat.all().len());
    for c in sat.all() {
        println!("{}", c);
    }
}
