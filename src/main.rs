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

/// Find the declared right triangle and its solved side lengths.
/// Returns `(tri, apex, v1, v2)`. Lengths are queried on demand.
fn right_triangle_ctx(
    facts: &checker::FactStore,
) -> Option<(String, char, char, char)> {
    for c in facts.all() {
        if let geo_lang::claim::Claim::PredVal { name, args, value } = &c {
            if name == "rightat" && args.len() == 1 {
                let apex = match value {
                    geo_lang::claim::Value::Point(p) => p.chars().next()?,
                    _ => continue,
                };
                let chars: Vec<char> = args[0].chars().collect();
                if chars.len() == 3 && chars.contains(&apex) {
                    let others: Vec<char> =
                        chars.iter().copied().filter(|&c| c != apex).collect();
                    if others.len() == 2 {
                        return Some((
                            args[0].clone(),
                            apex,
                            others[0],
                            others[1],
                        ));
                    }
                }
            }
        }
    }
    None
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
                                        "// Calc({}) = {}",
                                        checker::atom_display_len(lx),
                                        v
                                    );
                                    // Formal derivation via right-triangle
                                    // Pythagoras when applicable.
                                    if seg.chars().count() == 2 {
                                        if let Some((tri, apex, o1, o2)) =
                                            right_triangle_ctx(&goal_facts)
                                        {
                                            let tri_u = tri.to_uppercase();
                                            let s = seg.chars().collect::<Vec<char>>();
                                            if s.len() == 2 {
                                                let a = s[0];
                                                let b = s[1];
                                                let disp_seg = format!("{}{}", a.to_uppercase(), b.to_uppercase());
                                                let disp_hyp = format!("{}{}", o1.to_uppercase(), o2.to_uppercase());
                                                let is_hyp = (a == o1 && b == o2) || (a == o2 && b == o1);
                                                if is_hyp {
                                                    let l1d = format!("{}{}", apex.to_uppercase(), o1.to_uppercase());
                                                    let l2d = format!("{}{}", apex.to_uppercase(), o2.to_uppercase());
                                                    println!(
                                                        "// (RightAt({})={}) -> {}^2+{}^2={}^2 -> {}=sqrt({}^2+{}^2)={}",
                                                        tri_u, apex.to_uppercase(),
                                                        disp_seg, l1d, l2d,
                                                        disp_seg, l1d, l2d, v
                                                    );
                                                } else {
                                                    // It's a leg; find the other leg.
                                                    // The other leg goes from apex
                                                    // to the vertex NOT in seg.
                                                    let rem = if o1 != a && o1 != b { o1 } else { o2 };
                                                    let other_leg = format!("{}{}", apex.to_uppercase(), rem.to_uppercase());
                                                    let hv = symbolic::solve_len(
                                                        &geo_lang::claim::Claim::norm_seg(&disp_hyp),
                                                        &goal_facts,
                                                    );
                                                    let ov = symbolic::solve_len(
                                                        &geo_lang::claim::Claim::norm_seg(&other_leg),
                                                        &goal_facts,
                                                    );
                                                    if let (Some(hv), Some(ov)) = (hv, ov) {
                                                        println!(
                                                            "// (RightAt({})={}) -> {}^2+{}^2={}^2 -> {}=sqrt({}^2-{}^2)=sqrt({}-{})={}",
                                                            tri_u, apex.to_uppercase(),
                                                            disp_seg, other_leg, disp_hyp,
                                                            disp_seg, disp_hyp, other_leg,
                                                            hv*hv, ov*ov,
                                                            v
                                                        );
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                                None => {
                                    println!(
                                        "// Calc({}) = ? (length not determined)",
                                        checker::atom_display_len(lx)
                                    );
                                    println!(" Nothing");
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
                                        "// Calc(Angle({})) = {:.2}",
                                        angle_ref.to_uppercase(),
                                        deg
                                    );
                                    // Choose sin/cos/tan based on Sum goal context.
                                    let mut chained = false;
                                    let mut want_trig = String::from("cos");
                                    for g in &file.goals {
                                        if let Some(ast::ClaimExpr::Sum { rhs, .. }) = &g.claim {
                                            for t in rhs {
                                                if let Some(a) = &t.cos_angle {
                                                    if a.to_uppercase() == angle_ref.to_uppercase() {
                                                        want_trig = String::from("cos");
                                                        break;
                                                    }
                                                }
                                            }
                                        }
                                    }
                                    // Right triangle: choose sin/cos/tan.
                                    if let Some(t) = symbolic::find_triangle_with_vertex(
                                        &v.to_string(),
                                        &goal_facts,
                                    ) {
                                        let chars: Vec<char> = t.chars().collect();
                                        let right_apex = goal_facts.all().into_iter().find_map(|c| {
                                            match &c {
                                                geo_lang::claim::Claim::PredVal {
                                                    name,
                                                    args,
                                                    value,
                                                } if name == "rightat"
                                                    && args.len() == 1
                                                    && args[0] == *t =>
                                                {
                                                    match value {
                                                        geo_lang::claim::Value::Point(p) => {
                                                            p.chars().next()
                                                        }
                                                        _ => None,
                                                    }
                                                }
                                                _ => None,
                                            }
                                        });
                                        if let Some(r) = right_apex {
                                            if r != v && chars.contains(&r) {
                                                let w: char = *chars
                                                    .iter()
                                                    .find(|&&c| c != v && c != r)
                                                    .unwrap_or(&'?');
                                                let seg = |a: char, b: char| -> String {
                                                    format!("{}{}", a.to_uppercase(), b.to_uppercase())
                                                };
                                                let opp = geo_lang::claim::Claim::seg_key(
                                                    &r.to_string(), &w.to_string());
                                                let adj = geo_lang::claim::Claim::seg_key(
                                                    &v.to_string(), &r.to_string());
                                                let hyp = geo_lang::claim::Claim::seg_key(
                                                    &v.to_string(), &w.to_string());
                                                let ov = symbolic::solve_len(&opp, &goal_facts);
                                                let av = symbolic::solve_len(&adj, &goal_facts);
                                                let hv = symbolic::solve_len(&hyp, &goal_facts);
                                                let vu = v.to_uppercase();
                                                let reduced = |num: u32, den: u32| -> (u32, u32) {
                                                    let (mut a, mut b) = (num, den);
                                                    while b != 0 { let t = a % b; a = b; b = t; }
                                                    let g = if a == 0 { 1 } else { a };
                                                    (num / g, den / g)
                                                };
                                                let show = |trig: &str, ns: &str, ds: &str, nv: u32, dv: u32| {
                                                    let (fn_, fd) = reduced(nv, dv);
                                                    let rad = match trig {
                                                        "sin" => (nv as f64 / dv as f64).asin(),
                                                        "cos" => (nv as f64 / dv as f64).acos(),
                                                        _ => (nv as f64 / dv as f64).atan(),
                                                    };
                                                    let deg = rad * 180.0 / std::f64::consts::PI;
                                                    println!(
                                                        "// {}({})={}/{}={}/{} -> {}=arc{}({}/{})={:.2}",
                                                        trig, vu, ns, ds, fn_, fd,
                                                        vu, trig, fn_, fd, deg
                                                    );
                                                };
                                                if want_trig == "cos" {
                                                    if let (Some(a), Some(h)) = (av, hv) {
                                                        show("cos", &seg(v, r), &seg(v, w), a, h);
                                                        chained = true;
                                                    }
                                                } else if want_trig == "sin" {
                                                    if let (Some(o), Some(h)) = (ov, hv) {
                                                        show("sin", &seg(r, w), &seg(v, w), o, h);
                                                        chained = true;
                                                    }
                                                } else {
                                                    if let (Some(o), Some(a)) = (ov, av) {
                                                        show("tan", &seg(r, w), &seg(v, r), o, a);
                                                        chained = true;
                                                    }
                                                }
                                            }
                                        }
                                    }
                                    // Law-of-cosines fallback.
                                    if !chained {
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
                                                "({}) -> Angle({})={:.2} [law-of-cosines]",
                                                sides.join(" && "),
                                                angle_ref.to_uppercase(),
                                                deg
                                            );
                                        }
                                    }
                                    }
                                }
                                None => {
                                    println!(
                                        "// Calc(Angle({})) = ? (cannot be determined)",
                                        angle_ref.to_uppercase()
                                    );
                                    println!("Nothing");
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
                    let numeric_ok = symbolic::sum_solves(lhs, rhs, &goal_facts);
                    let trig_ok = !numeric_ok && symbolic::sum_solves_trig(lhs, rhs, &goal_facts);
                    if numeric_ok || trig_ok {
                        let display = checker::render_expr(claim);
                        if numeric_ok {
                            let premises = symbolic::sum_premises(lhs, rhs, &facts);
                            if premises.is_empty() {
                                println!("// {}", display);
                            } else {
                                println!(
                                    "// ({}) -> {}",
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
                let atoms = checker::claim_atoms(claim);
                if atoms.is_empty() {
                    println!("// invalid claim");
                    continue;
                }
                let displays = checker::atom_display_strings(claim);
                let mut goal_failed = false;
                for (g, display) in atoms.iter().zip(displays.iter()) {
                    if facts.contains(g) {
                        println!("{}", display);
                        continue;
                    }
                    match prover::prove_seeded(g, &goal_facts, &saturated, &rules) {
                        Some(p) => {
                            println!("{}", prover::render_chain(&p, Some(display)));
                            // Make the goal's claim available to later goals so
                            // they can reuse it instead of re-deriving it.
                            facts.add(g.clone(), checker::Origin::Proof(goal.index, 0));
                            saturated.add(g.clone(), checker::Origin::Proof(goal.index, 0));
                        }
                        None => {
                            println!("// {}  (cannot be proven)", display);
                            println!("Nothing");
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










