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
         \x20 geo_lang prove <file.geo> [claim]                prove every goal in the file\n\
         \x20 geo_lang help\n\
         \n\
         The checker validates each proof[N] block against the geometry rule\n\
         base and reports errors/warnings with source positions. The -e:\n\
         bypass downgrades the listed error kinds (GoalNotProven,\n\
         PremiseNotEstablished, WrongResult, ...) to assumptions (warnings).\n"
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

fn run_prove(path: &str, goal_arg: Option<&str>) -> ExitCode {
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
    let mut any_unproven = false;

    // One forward closure shared by every goal (single-claim path uses it too).
    let mut saturated = prover::forward_saturate(&facts, &rules);

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
            match prover::prove_seeded(goal, &facts, &saturated, &rules) {
                Some(p) => {
                    println!("{}: {}", label, display);
                    println!("chain: {}", prover::render_chain(&p, Some(display)));
                    println!("tree:");
                    println!("{}", prover::render_tree(&p, 1, Some(display)));
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
        for goal in &file.goals {
            // Apply this goal's scoped inputs (`inp[N]:` sections).
            let mut scoped_stmts: Vec<&geo_lang::ast::InputStmt> = Vec::new();
            for (idx, stmt) in &file.scoped_input {
                if *idx == goal.index {
                    scoped_stmts.push(stmt);
                }
            }
            // inputProperties[N][Scope]: Local keeps this goal's declarations
            // (and everything derived from them) private to the goal; Global
            // feeds them into the shared fact store.
            let scope = file
                .input_props
                .iter()
                .find(|p| p.index == goal.index)
                .map(|p| p.scope)
                .unwrap_or(ast::Scope::Global);
            let mut goal_facts = facts.clone();
            if !scoped_stmts.is_empty() {
                match scope {
                    ast::Scope::Local => {
                        checker::apply_input_statements(&mut goal_facts, &scoped_stmts);
                        saturated = prover::forward_saturate(&goal_facts, &rules);
                    }
                    ast::Scope::Global => {
                        checker::apply_input_statements(&mut facts, &scoped_stmts);
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
                            match symbolic::solve_len(&seg, &goal_facts) {
                                Some(v) => {
                                    println!(
                                        "goal {}: Calc({}) = {}",
                                        goal.index,
                                        checker::atom_display_len(lx),
                                        v
                                    );
                                    // Derivation chain from the numeric solver.
                                    let claim = geo_lang::claim::Claim::len_eq(&seg, v);
                                    if let Some(p) =
                                        symbolic::numeric_proof(&claim, &goal_facts)
                                    {
                                        println!(
                                            "  chain: {}",
                                            prover::render_chain(&p, None)
                                        );
                                    }
                                }
                                None => {
                                    println!(
                                        "goal {}: Calc({}) = ? (length not determined)",
                                        goal.index,
                                        checker::atom_display_len(lx)
                                    );
                                    any_unproven = true;
                                }
                            }
                        }
                        geo_lang::ast::CalcSpec::Angle(angle_ref) => {
                            // Angle(A B C): the vertex is the MIDDLE letter.
                            let v: char = angle_ref.chars().nth(1).unwrap_or('?');
                            let tri =
                                symbolic::find_triangle_with_vertex(&v.to_string(), &goal_facts);
                            match tri
                                .and_then(|t| symbolic::angle_degrees(&t, v, &goal_facts))
                            {
                                Some(deg) => {
                                    println!(
                                        "goal {}: Calc(Angle({})) = {:.2}°",
                                        goal.index,
                                        angle_ref.to_uppercase(),
                                        deg
                                    );
                                    // Law-of-cosines chain from the triangle's
                                    // three side lengths.
                                    if let Some(t) =
                                        symbolic::find_triangle_with_vertex(&v.to_string(), &goal_facts)
                                    {
                                        let chars: Vec<char> = t.chars().collect();
                                        let apex_pos = chars
                                            .iter()
                                            .position(|&c| c == v)
                                            .unwrap_or(0);
                                        let o1 = chars[(apex_pos + 1) % 3];
                                        let o2 = chars[(apex_pos + 2) % 3];
                                        let sides: Vec<String> = [
                                            (v, o1),
                                            (v, o2),
                                            (o1, o2),
                                        ]
                                        .iter()
                                        .filter_map(|(a, b)| {
                                            let key = geo_lang::claim::Claim::seg_key(
                                                &a.to_string(),
                                                &b.to_string(),
                                            );
                                            symbolic::solve_len(&key, &goal_facts).map(|n| {
                                                format!(
                                                    "{}{}={}",
                                                    a.to_uppercase(),
                                                    b.to_uppercase(),
                                                    n
                                                )
                                            })
                                        })
                                        .collect();
                                        if sides.len() == 3 {
                                            println!(
                                                "  chain: ({}) -> Angle({})={:.2}°  [law-of-cosines]",
                                                sides.join(" && "),
                                                angle_ref.to_uppercase(),
                                                deg
                                            );
                                        }
                                    }
                                }
                                None => {
                                    println!(
                                        "goal {}: Calc(Angle({})) = ? (cannot be determined)",
                                        goal.index,
                                        angle_ref.to_uppercase()
                                    );
                                    any_unproven = true;
                                }
                            }
                        }
                    }
                }
                continue;
            }
            if let Some(claim) = &goal.claim {
                // Trig sum goals are verified numerically.
                if let ast::ClaimExpr::Sum { lhs, rhs, .. } = claim {
                    if symbolic::sum_solves(lhs, rhs, &goal_facts) {
                        let display = checker::render_expr(claim);
                        let premises = symbolic::sum_premises(lhs, rhs, &goal_facts);
                        if premises.is_empty() {
                            println!("goal {}: {}  (numeric)", goal.index, display);
                        } else {
                            println!("goal {}: {}", goal.index, display);
                            println!(
                                "  chain: ({}) -> {}  [numeric]",
                                premises.join(" && "),
                                display
                            );
                        }
                    } else {
                        println!(
                            "goal {}: {}  (cannot be proven)",
                            goal.index,
                            checker::render_expr(claim)
                        );
                        any_unproven = true;
                    }
                    continue;
                }
                let atoms = checker::claim_atoms(claim);
                if atoms.is_empty() {
                    println!("goal {}: invalid claim", goal.index);
                    continue;
                }
                let displays = checker::atom_display_strings(claim);
                let multi = atoms.len() > 1;
                let mut goal_failed = false;
                for (i, (g, display)) in atoms.iter().zip(displays.iter()).enumerate() {
                    let label = if multi {
                        format!("goal {} atom {}", goal.index, i + 1)
                    } else {
                        format!("goal {}", goal.index)
                    };
                    if facts.contains(g) {
                        println!("{}: {}  (already established)", label, display);
                        continue;
                    }
                    match prover::prove_seeded(g, &goal_facts, &saturated, &rules) {
                        Some(p) => {
                            println!("{}: {}", label, display);
                            println!("  chain: {}", prover::render_chain(&p, Some(display)));
                            let mut tree = prover::render_tree(&p, 2, Some(display));
                            if tree.ends_with('\n') {
                                tree.pop();
                            }
                            println!("  {}", tree.replace("\n", "\n  "));
                            // Make the goal's claim available to later goals so
                            // they can reuse it instead of re-deriving it.
                            facts.add(g.clone(), checker::Origin::Proof(goal.index, 0));
                            saturated.add(g.clone(), checker::Origin::Proof(goal.index, 0));
                        }
                        None => {
                            println!("{}: {}  (cannot be proven)", label, display);
                            goal_failed = true;
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
            let positional: Vec<&String> =
                args.iter().skip(2).filter(|a| !a.starts_with("-e:")).collect();
            if positional.len() < 1 || positional.len() > 2 {
                eprintln!("usage: geo_lang prove <file.geo> [claim]");
                return ExitCode::from(2);
            }
            run_prove(
                positional[0],
                positional.get(1).map(|s| s.as_str()),
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


