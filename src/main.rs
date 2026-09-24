//! geo_lang: a proof checker and prover for the `.geo` geometry language.

use geo_lang::{ast, checker, diag, parser, prover, rules, symbolic};

use std::io::Read;
use std::process::ExitCode;

fn print_usage() {
    println!(
        "geo_lang - a proof checker and prover for the .geo geometry language\n\
         \n\
         USAGE:\n\
         \x20 geo_lang check <file.geo> [ -e:Error1,Error2 ]   check proofs in a file\n\
         \x20 geo_lang prove <file.geo> [claim] [-disable:Rule1,Rule2]  prove every goal in the file\n\
         \x20 geo_lang help\n\
         \n\
         The checker validates each proof[N] block against the geometry rule\n\
         base and reports errors/warnings with source positions. The -e:\n\
         bypass downgrades the listed error kinds (GoalNotProven,\n\
         PremiseNotEstablished, WrongResult, ...) to assumptions (warnings).\n\
         The -disable: flag excludes specific rules from the prover (e.g.\n\
         -disable:isosceles-altitude,median-midpoint).\n"
    );
}

fn read_source(path: &str) -> Result<(String, String), String> {
    let mut f = std::fs::File::open(path).map_err(|e| format!("cannot open {}: {}", path, e))?;
    let mut s = String::new();
    f.read_to_string(&mut s).map_err(|e| format!("cannot read {}: {}", path, e))?;
    Ok((path.to_string(), s))
}

/// Collect the `-e:Name1,Name2` bypass list from the remaining arguments.
fn bypass_names(args: &[String]) -> Vec<String> {
    let mut out = Vec::new();
    for a in args {
        if let Some(rest) = a.strip_prefix("-e:") {
            out.extend(rest.split(',').map(|s| s.trim().to_string()).filter(|s| !s.is_empty()));
        }
    }
    out
}

/// Collect the `-disable:Rule1,Rule2` list from the remaining arguments.
fn disable_rules(args: &[String]) -> Vec<String> {
    let mut out = Vec::new();
    for a in args {
        if let Some(rest) = a.strip_prefix("-disable:") {
            out.extend(rest.split(',').map(|s| s.trim().to_string()).filter(|s| !s.is_empty()));
        }
    }
    out
}

fn run_check(path: &str, bypass: &[String]) -> ExitCode {
    let (source, src_text) = match read_source(path) {
        Ok(x) => x,
        Err(e) => {
            eprintln!("{}", e);
            return ExitCode::from(2);
        }
    };

    let file = match parser::parse(&source, &src_text) {
        Ok(f) => f,
        Err(e) => {
            eprintln!(
                "{}:{}:{}: error: {}",
                source, e.pos.line, e.pos.col, e.msg
            );
            return ExitCode::from(1);
        }
    };

    let diags = diag::bypass_errors(checker::check(&file), bypass);
    for d in &diags {
        println!("{}", diag::render_diag(&file.source, &file.lines, d));
        println!();
    }

    let errors = diags.iter().filter(|d| d.is_error()).count();
    if errors > 0 {
        println!("{} error(s) found", errors);
        ExitCode::from(1)
    } else {
        println!("proof OK");
        ExitCode::SUCCESS
    }
}

fn parse_single_claim(text: &str) -> Result<Vec<ast::ClaimExpr>, String> {
    let src = format!("prove:\n1. {}\n", text);
    let file = parser::parse("claim", &src).map_err(|e| e.msg)?;
    let goal = file.goals.first().ok_or("no goal parsed")?;
    let claim = goal.claim.as_ref().ok_or("nothing to prove")?;
    Ok(vec![claim.clone()])
}

/// Find the declared right triangle and its solved side lengths.
/// Returns `(tri, apex, v1, v2)`. Lengths are queried on demand.

fn run_prove(path: &str, goal_arg: Option<&str>, disabled: &[String], dump_depth: Option<usize>) -> ExitCode {
    let (source, src_text) = match read_source(path) {
        Ok(x) => x,
        Err(e) => {
            eprintln!("{}", e);
            return ExitCode::from(2);
        }
    };

    let file = match parser::parse(&source, &src_text) {
        Ok(f) => f,
        Err(e) => {
            eprintln!(
                "{}:{}:{}: error: {}",
                source, e.pos.line, e.pos.col, e.msg
            );
            return ExitCode::from(1);
        }
    };

    // Establish facts from the input section, then reuse the claims
    // established inside explicit proof blocks (Global scope only, matching
    // the checker; Scope=Local proof internals stay hidden).
    let mut facts = checker::build_facts_from_input(&file);
    let _ = checker::apply_proofs(&file, &mut facts);
    let rules = rules::rule_base();
    // Build disabled set; rules are kept for chain fallback.
    let disabled_set: std::collections::HashSet<&str> = if !disabled.is_empty() {
        let set: std::collections::HashSet<&str> = disabled.iter().map(|s| s.as_str()).collect();
        let count = rules.iter().filter(|r| set.contains(&*r.id)).count();
        if count > 0 {
            println!("// Disabled {} rule(s): {}", count, disabled.join(", "));
        }
        set
    } else {
        std::collections::HashSet::new()
    };
    let disabled_opt = if disabled_set.is_empty() { None } else { Some(&disabled_set) };
    let mut any_unproven = false;

    // Forward saturation uses only enabled rules.
    let enabled_rules: Vec<&rules::Rule> = rules.iter()
        .filter(|r| !disabled_set.contains(&*r.id))
        .collect();
    let enabled_rules_owned: Vec<rules::Rule> = enabled_rules.into_iter().cloned().collect();
    let mut saturated = prover::forward_saturate_d(&facts, &enabled_rules_owned, dump_depth);

    if let Some(goal_text) = goal_arg {
        let exprs = match parse_single_claim(goal_text) {
            Ok(e) => e,
            Err(e) => {
                eprintln!("error: cannot parse claim `{}`: {}", goal_text, e);
                return ExitCode::from(2);
            }
        };
        let expr = &exprs[0];
        let atoms = checker::claim_atoms(expr);
        if atoms.is_empty() {
            eprintln!("error: claim `{}` contains no atoms", goal_text);
            return ExitCode::from(2);
        }
        let displays = checker::atom_display_strings(expr);
        let multi = atoms.len() > 1;
        let mut any_fail = false;
        for (i, (goal, display)) in atoms.iter().zip(displays.iter()).enumerate() {
            let label = if multi {
                format!("atom {}", i + 1)
            } else {
                "goal".to_string()
            };
            if facts.contains(goal) {
                println!("{}: {}  (already established)", label, display);
                continue;
            }
            match prover::prove_seeded(goal, &facts, &saturated, &rules, disabled_opt) {
                Some(p) => {
                    let tree = prover::render_tree(&p, 0, Some(display));
                    for line in tree.lines() {
                        println!("// {}", line);
                    }
                    let chain = prover::render_chain(&p, Some(display));
                    println!("{}", chain);
                }
                None => {
                    println!("cannot prove: {}", display);
                    any_fail = true;
                }
            }
        }
        if any_fail {
            ExitCode::from(1)
        } else {
            ExitCode::SUCCESS
        }
    } else {
        let mut last_proof_idx: Option<u32> = None;
        for goal in &file.goals {
                        // Apply this goal's scoped inputs (`inp[N]:` sections).
            let mut scoped_stmts: Vec<&geo_lang::ast::InputStmt> = Vec::new();
            for (idx, stmt) in &file.scoped_input {
                if *idx == goal.index {
                    scoped_stmts.push(stmt);
                }
            }
            let mut goal_facts = facts.clone();
            if last_proof_idx != Some(goal.index) {
                println!("proof[{}]:", goal.index);
                last_proof_idx = Some(goal.index);
            }
            // inputProperties[N][Scope]: strict resolution.
            //   Global (default): inp[N] statements feed the shared store.
            //   Local: inp[N] statements are private to goal N's proof —
            //     applied to a throwaway copy, discarded afterwards.
            let scope = file
                .input_props
                .iter()
                .find(|p| p.index == goal.index)
                .map(|p| p.scope)
                .unwrap_or(ast::Scope::Global);
            if !scoped_stmts.is_empty() {
                match scope {
                    ast::Scope::Local => {
                        checker::apply_input_statements(&mut goal_facts, &scoped_stmts);
                        saturated = prover::forward_saturate(&goal_facts, &rules);
                    }
                    ast::Scope::Global => {
                        checker::apply_input_statements(&mut facts, &scoped_stmts);
                        checker::derive_perpendicular_foot_midpoints(&mut facts);
                        goal_facts = facts.clone();
                        saturated = prover::forward_saturate(&facts, &rules);
                    }
                }
            }


            // `Calc(...)` goals evaluate numerically instead of proving.
            if !goal.calcs.is_empty() {
                for c in &goal.calcs {
                    match c {
                        geo_lang::ast::CalcSpec::Len(lx) => {
                            let seg = lx.seg();
                            let display = checker::atom_display_len(lx);
                            // Try to build a formal proof tree via numeric_proof.
                            let claim = geo_lang::claim::Claim::len_eq(
                                &geo_lang::claim::Claim::norm_seg(&seg),
                                symbolic::solve_len(&seg, &goal_facts).unwrap_or(0),
                            );
                            if let Some(p) = geo_lang::prover::prove_seeded(
                                &claim, &goal_facts, &saturated, &rules, disabled_opt,
                            ) {
                                let tree = geo_lang::prover::render_tree(&p, 0, Some(&display));
                                for line in tree.lines() {
                                    println!("// {}", line);
                                }
                                let chain = geo_lang::prover::render_chain(&p, None);
                                println!("{}", chain);
                            } else if let Some(v) = symbolic::solve_len(&seg, &goal_facts) {
                                // Fallback: just print the value.
                                println!("// Calc({}) = {}", display, v);
                            } else {
                                println!("// Calc({}) = ? (length not determined)", display);
                                println!(" Nothing");
                                any_unproven = true;
                            }
                        }
                        geo_lang::ast::CalcSpec::Angle(angle_ref) => {
                            // Angle(A B C): the vertex is the MIDDLE letter.
                            // For single-letter vertex (e.g., Calc(Angle(U))), find
                            // which triangle contains it.
                            let v: char = if angle_ref.len() >= 3 {
                                angle_ref.chars().nth(1).unwrap_or('?')
                            } else {
                                angle_ref.chars().next().unwrap_or('?')
                            };
                            let display = format!("Angle({})", angle_ref.to_uppercase());
                            // Try to build a formal proof tree via angle_proof.
                            if let Some(p) = symbolic::angle_proof(&v.to_string(), &goal_facts) {
                                let tree = geo_lang::prover::render_tree(&p, 0, Some(&display));
                                for line in tree.lines() {
                                    println!("// {}", line);
                                }
                                let chain = geo_lang::prover::render_chain(&p, None);
                                println!("{}", chain);
                            } else if let Some((_, deg)) = symbolic::angle_degrees_any(&v.to_string(), &goal_facts) {
                                // Fallback: just print the value.
                                println!("// Calc(Angle({})) = {:.2}", angle_ref.to_uppercase(), deg);
                            } else {
                                println!(
                                    "// Calc(Angle({})) = ? (cannot be determined)",
                                    angle_ref.to_uppercase()
                                );
                                println!(" Nothing");
                                any_unproven = true;
                            }
                        }
                    }
                }
                continue;
            }
            if let Some(claim) = &goal.claim {
                // Trig sum goals are verified numerically.
                if let ast::ClaimExpr::Sum { lhs, rhs, .. } = claim {
                    let numeric_ok = symbolic::sum_solves(lhs, rhs, &goal_facts);
                    let trig_ok = !numeric_ok && symbolic::sum_solves_trig(lhs, rhs, &goal_facts);
                    if numeric_ok || trig_ok {
                        let display = checker::render_expr(claim);
                        if numeric_ok {
                            let premises = symbolic::sum_premises(lhs, rhs, &facts);
                            if premises.is_empty() {
                                println!("{}", display);
                            } else {
                                println!(
                                    "({}) -> {}",
                                    premises.join(" && "),
                                    display
                                );
                            }
                        } else {
                            // Symbolic: find the right triangle and show the
                            // cos-substitution + pythagoras derivation.
                            println!("// {}", display);
                            let mut shown = false;
                            for c in goal_facts.all() {
                                if let geo_lang::claim::Claim::PredVal { name, args, value } = &c {
                                    if name == "rightat" && args.len() == 1 {
                                        let apex = match value {
                                            geo_lang::claim::Value::Point(p) => p.chars().next(),
                                            _ => None,
                                        };
                                        if let Some(apex) = apex {
                                            let steps = symbolic::sum_trig_steps(
                                                lhs, rhs, &args[0], apex,
                                            );
                                            for s in &steps {
                                                println!("{}", s);
                                            }
                                            shown = true;
                                            break;
                                        }
                                    }
                                }
                            }
                            if !shown {
                                println!("// (symbolic-trig)");
                            }
                        }
                    } else {
                        println!(
                            "// {}  (cannot be proven)",
                            checker::render_expr(claim)
                        );
                        println!("Nothing");
                        any_unproven = true;
                    }
                    continue;
                }
                // EqChain goals with compound expressions (law of cosines etc.)
                if let ast::ClaimExpr::EqChain { items, .. } = claim {
                    let display = checker::render_expr(claim);
                    // Try law of cosines proof
                    if let Some(p) = symbolic::law_of_cosines_proof(items, &goal_facts) {
                        let tree = prover::render_tree(&p, 0, Some(&display));
                        for line in tree.lines() {
                            println!("// {}", line);
                        }
                        let chain = prover::render_chain(&p, Some(&display));
                        println!("{}", chain);
                        continue;
                    }
                    // Rectangle diagonal identity: AE²+BE²+CE²+DE²=AB²+BC².
                    if let Some(p) = symbolic::rectangle_diagonal_proof(items, &goal_facts) {
                        let tree = prover::render_tree(&p, 0, Some(&display));
                        for line in tree.lines() {
                            println!("// {}", line);
                        }
                        let chain = prover::render_chain(&p, Some(&display));
                        println!("{}", chain);
                        continue;
                    }
                    // Numeric evaluation: compute both sides and check equality.
                    if items.len() >= 2 {
                        // Try exact rational comparison first.
                        let rat_vals: Vec<Option<symbolic::EXRat>> = items
                            .iter()
                            .map(|e| symbolic::eval_len_expr_ratio(e, &goal_facts))
                            .collect();
                        let rat_ok = rat_vals.iter().all(|v| v.is_some())
                            && rat_vals[1..].iter().all(|v| *v.as_ref().unwrap() == *rat_vals[0].as_ref().unwrap());
                        if rat_ok {
                            // Show derivation trees for segment items.
                            for item in items.iter() {
                                let seg_str = item.seg();
                                if !seg_str.is_empty() {
                                    if let Some(p) = symbolic::ratio_derivation_proof(&seg_str, &goal_facts) {
                                        let display = checker::render_len_expr(item);
                                        let tree = prover::render_tree(&p, 1, Some(&display));
                                        for line in tree.lines() {
                                            println!("// {}", line);
                                        }
                                    }
                                }
                            }
                            let parts: Vec<String> = items
                                .iter()
                                .map(|e| checker::render_len_expr(e))
                                .collect();
                            println!("{}", parts.join("="));
                            continue;
                        }
                        // Fall back to f64 comparison for trig/irrationals.
                        let vals: Vec<Option<f64>> = items
                            .iter()
                            .map(|e| symbolic::eval_len_expr(e, &goal_facts))
                            .collect();
                        if vals.iter().all(|v| v.is_some()) {
                            let v0 = vals[0].unwrap();
                            if vals[1..].iter().all(|v| (v.unwrap() - v0).abs() < 1e-9) {
                                let parts: Vec<String> = items
                                    .iter()
                                    .map(|e| checker::render_len_expr(e))
                                    .collect();
                                println!("{}", parts.join("="));
                                continue;
}
                    }
                }
                // Symbolic trig evaluation for EqChain (like sum_solves_trig but for EqChain).
                let display = checker::render_expr(claim);
                if let Some((tri, apex)) = symbolic::eq_chain_solves_trig(items, &goal_facts) {
                    println!("// {}", display);
                    let steps = symbolic::eq_chain_trig_steps(items, &tri, apex);
                    for s in &steps {
                        println!("{}", s);
                    }
                    let parts: Vec<String> = items
                        .iter()
                        .map(|e| checker::render_len_expr(e))
                        .collect();
                    println!("{}", parts.join("="));
                    continue;
                }
                }
                // Try to convert product equality to RatioEq and prove: a*b = c*d -> a/c = d/b
                if let ast::ClaimExpr::EqChain { items, .. } = claim {
                    if items.len() == 2 {
                        let try_prove_as_ratio = |lhs: &ast::LenExpr, rhs: &ast::LenExpr| -> bool {
                            let (seg_a, seg_b, seg_c, seg_d) = match (lhs, rhs) {
                                (ast::LenExpr::Mul(l1, r1), ast::LenExpr::Mul(l2, r2)) => {
                                    let a = match l1.as_ref() { ast::LenExpr::Seg(s) => s.clone(), _ => return false };
                                    let b = match r1.as_ref() { ast::LenExpr::Seg(s) => s.clone(), _ => return false };
                                    let c = match l2.as_ref() { ast::LenExpr::Seg(s) => s.clone(), _ => return false };
                                    let d = match r2.as_ref() { ast::LenExpr::Seg(s) => s.clone(), _ => return false };
                                    (a, b, c, d)
                                }
                                _ => return false,
                            };
                            // a*b = c*d  <=>  a/c = d/b  <=>  a/b = c/d (various forms)
                            // Try a/c = d/b
                            let ratio_claim = geo_lang::claim::Claim::ratio_eq(
                                &geo_lang::claim::RatioExpr::Quot {
                                    num: geo_lang::claim::RatioAtom::Seg(seg_a.clone()),
                                    den: geo_lang::claim::RatioAtom::Seg(seg_c.clone()),
                                },
                                &geo_lang::claim::RatioExpr::Quot {
                                    num: geo_lang::claim::RatioAtom::Seg(seg_d.clone()),
                                    den: geo_lang::claim::RatioAtom::Seg(seg_b.clone()),
                                },
                            );
                            if let Some(rp) = prover::prove_seeded(&ratio_claim, &goal_facts, &saturated, &rules, disabled_opt) {
                                let display = checker::render_expr(claim);
                                println!("// {}", display);
                                let tree = prover::render_tree(&rp, 0, None);
                                for line in tree.lines() {
                                    println!("// {}", line);
                                }
                                let chain = prover::render_chain(&rp, None);
                                println!("{}", chain);
                                println!("{}", display);
                                return true;
                            }
                            // Try a/b = c/d
                            let ratio_claim2 = geo_lang::claim::Claim::ratio_eq(
                                &geo_lang::claim::RatioExpr::Quot {
                                    num: geo_lang::claim::RatioAtom::Seg(seg_a.clone()),
                                    den: geo_lang::claim::RatioAtom::Seg(seg_b.clone()),
                                },
                                &geo_lang::claim::RatioExpr::Quot {
                                    num: geo_lang::claim::RatioAtom::Seg(seg_c.clone()),
                                    den: geo_lang::claim::RatioAtom::Seg(seg_d.clone()),
                                },
                            );
                            if let Some(rp) = prover::prove_seeded(&ratio_claim2, &goal_facts, &saturated, &rules, disabled_opt) {
                                let display = checker::render_expr(claim);
                                println!("// {}", display);
                                let tree = prover::render_tree(&rp, 0, None);
                                for line in tree.lines() {
                                    println!("// {}", line);
                                }
                                let chain = prover::render_chain(&rp, None);
                                println!("{}", chain);
                                println!("{}", display);
                                return true;
                            }
                            false
                        };
                        if try_prove_as_ratio(&items[0], &items[1]) || try_prove_as_ratio(&items[1], &items[0]) {
                            continue;
                        }
                    }
                }
                let atoms = checker::claim_atoms(claim);
                if atoms.is_empty() {
                    // EqChain with arithmetic that we can't decompose - not invalid, just not provable yet.
                    if let ast::ClaimExpr::EqChain { .. } = claim {
                        println!("// {}  (cannot be proven)", checker::render_expr(claim));
                        println!("Nothing");
                    } else {
                        println!("// invalid claim");
                    }
                    continue;
                }
                let displays = checker::atom_display_strings(claim);
                let mut goal_failed = false;
                for (g, display) in atoms.iter().zip(displays.iter()) {
                    // Try to find a proof chain even if the fact is already
                    // established (e.g. from auto-derivation), so the user
                    // can see the derivation steps.
                    match prover::prove_seeded(g, &goal_facts, &saturated, &rules, disabled_opt) {
                        Some(p) => {
                            let tree = prover::render_tree(&p, 0, Some(display));
                            for line in tree.lines() {
                                println!("// {}", line);
                            }
                            let chain = prover::render_chain(&p, Some(display));
                            println!("{}", chain);
                            facts.add(g.clone(), checker::Origin::Proof(goal.index, 0));
                            saturated.add(g.clone(), checker::Origin::Proof(goal.index, 0));
                        }
                        None => {
                            if facts.contains(g) {
                                // Already established but no chain found —
                                // show as a derived fact.
                                println!("{}  (derived)", display);
                            } else {
                                println!("// {}  (cannot be proven)", display);
                                println!("Nothing");
                                goal_failed = true;
                            }
                        }
                    }
                }
                if goal_failed {
                    any_unproven = true;
                }
            }
        }
        if any_unproven {
            ExitCode::from(1)
        } else {
            ExitCode::SUCCESS
        }
    }
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        print_usage();
        return ExitCode::from(2);
    }
    match args[1].as_str() {
        "check" => {
            let bypass = bypass_names(&args[2..]);
            let path = args
                .iter()
                .skip(2)
                .find(|a| !a.starts_with("-e:"))
                .cloned();
            let Some(path) = path else {
                eprintln!("usage: geo_lang check <file.geo> [-e:Error1,Error2]");
                return ExitCode::from(2);
            };
            run_check(&path, &bypass)
        }
        "prove" => {
            let disable = disable_rules(&args[2..]);
            let dump_depth = args.iter().skip(2)
                .find(|a| a.starts_with("-dump-facts=") || a.starts_with("--dump-facts="))
                .and_then(|a| a.split('=').nth(1))
                .and_then(|s| s.parse::<usize>().ok());
            let positional: Vec<&String> =
                args.iter().skip(2).filter(|a| !a.starts_with("-e:") && !a.starts_with("-disable:") && !a.starts_with("-dump-facts=") && !a.starts_with("--dump-facts=")).collect();
            if positional.len() < 1 || positional.len() > 2 {
                eprintln!("usage: geo_lang prove <file.geo> [claim] [-disable:Rule1,Rule2] [-dump-facts=N]");
                return ExitCode::from(2);
            }
            run_prove(
                positional[0],
                positional.get(1).map(|s| s.as_str()),
                &disable,
                dump_depth,
            )
        }
        "help" | "--help" | "-h" => {
            print_usage();
            ExitCode::SUCCESS
        }
        other => {
            eprintln!("unknown command: {}", other);
            print_usage();
            ExitCode::from(2)
        }
    }
}
