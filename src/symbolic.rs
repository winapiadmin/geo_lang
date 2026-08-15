//! Numeric (symbolic) solver for lengths and ratios.
//!
//! Given the numeric length facts (`AD=3`, `Distance(A,H)=7`) and the
//! geometric incidence facts, this module derives concrete lengths:
//!
//! * segment equality propagates lengths,
//! * in an isosceles triangle the two legs are equal,
//! * collinear points satisfy segment addition (`AH + HC = AC`),
//! * a perpendicular from a vertex to a line makes right triangles whose
//!   third side follows from the Pythagorean theorem.
//!
//! It also reduces ratios of known lengths to reduced fractions, so `AD/DB`
//! and `AE/EC` are seen equal when `3/2 = 6/4` (cross-multiplication is
//! implicit in the reduction).

use crate::checker::FactStore;
use crate::claim::{Claim, RatioAtom, RatioExpr};
use crate::prover::Proof;
use std::collections::HashMap;

/// How a numeric value was derived: the rule name and the numeric claims it
/// used as inputs. The inputs are `Claim::LenEq` or `Claim::SqEq` facts that
/// can themselves be explained recursively.
#[derive(Debug, Clone)]
struct NumStep {
    rule: &'static str,
    inputs: Vec<Claim>,
}

#[derive(Debug, Default)]
pub struct NumericEnv {
    /// Direct lengths: `norm_seg -> length`.
    pub lens: HashMap<String, u32>,
    /// Squared lengths: `norm_seg -> length^2` (for non-perfect squares).
    pub sq: HashMap<String, u32>,
    /// Derivation of each known length.
    len_steps: HashMap<String, NumStep>,
    /// Derivation of each known squared length.
    sq_steps: HashMap<String, NumStep>,
}

fn gcd(mut a: u32, mut b: u32) -> u32 {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a.max(1)
}

fn isqrt(n: u32) -> Option<u32> {
    let r = (n as f64).sqrt() as u32;
    if r * r == n {
        Some(r)
    } else if (r + 1) * (r + 1) == n {
        Some(r + 1)
    } else {
        None
    }
}

fn norm_pts(seg: &str) -> Option<(char, char)> {
    let chars: Vec<char> = Claim::norm_seg(seg).chars().collect();
    if chars.len() == 2 {
        Some((chars[0], chars[1]))
    } else {
        None
    }
}

fn seg_of(a: char, b: char) -> String {
    Claim::norm_seg(&format!("{}{}", a, b))
}

fn record_len(env: &mut NumericEnv, seg: &str, n: u32, rule: &'static str, inputs: Vec<Claim>) {
    let s = Claim::norm_seg(seg);
    if env.lens.get(&s).copied() != Some(n) {
        env.lens.insert(s.clone(), n);
    }
    env.sq.insert(s.clone(), n * n);
    env.len_steps
        .entry(s)
        .or_insert(NumStep { rule, inputs });
}

fn record_sq(env: &mut NumericEnv, seg: &str, v: u32, rule: &'static str, inputs: Vec<Claim>) {
    let s = Claim::norm_seg(seg);
    let had_len = env.lens.get(&s).is_some();
    if env.sq.get(&s).copied() != Some(v) {
        env.sq.insert(s.clone(), v);
    }
    if let Some(r) = isqrt(v) {
        if env.lens.get(&s).copied() != Some(r) {
            env.lens.insert(s.clone(), r);
        }
    }
    // Only keep a *derivation* for the square when the segment's length is
    // not directly known: otherwise the square is trivially the length
    // squared, and keeping a Pythagoras step for it could create a circular
    // explanation (e.g. AB^2 = BH^2 + AH^2 re-using the BH^2 it helped find).
    if !had_len {
        env.sq_steps
            .entry(s)
            .or_insert(NumStep { rule, inputs });
    }
}

fn get_len(env: &NumericEnv, seg: &str) -> Option<u32> {
    env.lens.get(&Claim::norm_seg(seg)).copied()
}

fn get_sq(env: &NumericEnv, seg: &str) -> Option<u32> {
    env.sq.get(&Claim::norm_seg(seg)).copied()
}

/// Compute all derivable lengths to a fixpoint.
pub fn compute(facts: &FactStore) -> NumericEnv {
    let mut env = NumericEnv::default();
    for c in facts.all() {
        if let Claim::LenEq(seg, n) = c {
            // Direct inputs: keep a `given` step so later derivations cannot
            // overwrite them (which could introduce circular explanations).
            let s = Claim::norm_seg(&seg);
            env.lens.insert(s.clone(), n);
            env.sq.insert(s.clone(), n * n);
            env.len_steps.insert(
                s,
                NumStep {
                    rule: "given",
                    inputs: Vec::new(),
                },
            );
        }
    }

    let claims = facts.all();
    // Points lying on each segment (line), including the segment endpoints.
    let mut on: HashMap<String, Vec<char>> = HashMap::new();
    for c in &claims {
        if let Claim::On(p, s) = c {
            if let Some((a, b)) = norm_pts(s) {
                let key = seg_of(a, b);
                let pch = Claim::norm_ref(p).chars().next().unwrap_or('\0');
                let list = on.entry(key).or_default();
                if !list.contains(&pch) {
                    list.push(pch);
                }
            }
        }
    }

    for _ in 0..64 {
        let before = env.lens.len() + env.sq.len();
        propagate(&mut env, &claims, &on);
        let after = env.lens.len() + env.sq.len();
        if after == before {
            break;
        }
    }
    env
}

fn propagate(
    env: &mut NumericEnv,
    claims: &[Claim],
    on: &HashMap<String, Vec<char>>,
) {
    // Segment equality propagates lengths.
    for c in claims {
        if let Claim::SegEq(a, b) = c {
            if let Some(n) = get_len(env, a) {
                record_len(env, b, n, "segment-equality", vec![Claim::len_eq(a, n)]);
            }
            if let Some(n) = get_len(env, b) {
                record_len(env, a, n, "segment-equality", vec![Claim::len_eq(b, n)]);
            }
            if let Some(s) = get_sq(env, a) {
                record_sq(env, b, s, "segment-equality", vec![Claim::sq_eq(a, s)]);
            }
            if let Some(s) = get_sq(env, b) {
                record_sq(env, a, s, "segment-equality", vec![Claim::sq_eq(b, s)]);
            }
        }
    }

    // In an isosceles triangle the legs are equal: apex `a` with base `bc`.
    for c in claims {
        if let Claim::IsoscelesAt(t, a) = c {
            let tc: Vec<char> = Claim::norm_tri(t).chars().collect();
            let ac: Vec<char> = Claim::norm_ref(a).chars().collect();
            if tc.len() == 3 && ac.len() == 1 {
                let apex = ac[0];
                let base: Vec<char> = tc.iter().copied().filter(|&p| p != apex).collect();
                if base.len() == 2 {
                    let leg1 = seg_of(apex, base[0]);
                    let leg2 = seg_of(apex, base[1]);
                    if let Some(n) = get_len(env, &leg1) {
                        record_len(
                            env,
                            &leg2,
                            n,
                            "isosceles-legs",
                            vec![Claim::len_eq(&leg1, n)],
                        );
                    }
                    if let Some(n) = get_len(env, &leg2) {
                        record_len(
                            env,
                            &leg1,
                            n,
                            "isosceles-legs",
                            vec![Claim::len_eq(&leg2, n)],
                        );
                    }
                }
            }
        }
    }

    // Segment addition: for a point `p` on segment `ab`, len(ab) is the sum
    // (or difference) of the two sub-segments.
    for c in claims {
        if let Claim::On(p, s) = c {
            if let Some((a, b)) = norm_pts(s) {
                let ab = seg_of(a, b);
                let pch = Claim::norm_ref(p).chars().next().unwrap_or('\0');
                if pch != a && pch != b {
                    let ap = seg_of(a, pch);
                    let pb = seg_of(pch, b);
                    match (get_len(env, &ap), get_len(env, &pb)) {
                        (Some(x), Some(y)) => record_len(
                            env,
                            &ab,
                            x + y,
                            "segment-addition",
                            vec![Claim::len_eq(&ap, x), Claim::len_eq(&pb, y)],
                        ),
                        _ => {}
                    }
                    if let Some(ab_len) = get_len(env, &ab) {
                        if let Some(x) = get_len(env, &ap) {
                            if ab_len >= x {
                                record_len(
                                    env,
                                    &pb,
                                    ab_len - x,
                                    "segment-subtraction",
                                    vec![Claim::len_eq(&ab, ab_len), Claim::len_eq(&ap, x)],
                                );
                            }
                        }
                        if let Some(y) = get_len(env, &pb) {
                            if ab_len >= y {
                                record_len(
                                    env,
                                    &ap,
                                    ab_len - y,
                                    "segment-subtraction",
                                    vec![Claim::len_eq(&ab, ab_len), Claim::len_eq(&pb, y)],
                                );
                            }
                        }
                    }
                }
            }
        }
    }

    // Pythagoras: `xy` perpendicular to `zw` with foot `h` on `zw` makes a
    // right triangle `(x, p, h)` for every point `p` on the line `zw`.
    for c in claims {
        if let Claim::PredVal { name, args, .. } = c {
            if name != "isperpendicular" || args.len() != 2 {
                continue;
            }
            let (x, y) = match norm_pts(&args[0]) {
                Some(p) => p,
                None => continue,
            };
            let (z, w) = match norm_pts(&args[1]) {
                Some(p) => p,
                None => continue,
            };
            let zw = seg_of(z, w);
            let line_pts: Vec<char> = {
                let mut pts = vec![z, w];
                if let Some(list) = on.get(&zw) {
                    pts.extend(list.iter().copied());
                }
                pts
            };
            // The foot is the endpoint of `xy` that lies on the line `zw`.
            let foot = if line_pts.contains(&x) && x != y {
                x
            } else if line_pts.contains(&y) {
                y
            } else {
                continue;
            };
            let other = if foot == x { y } else { x };
            let leg_other = seg_of(other, foot);
            for &p in &line_pts {
                if p == foot {
                    continue;
                }
                let leg_p = seg_of(p, foot);
                let hyp = seg_of(other, p);
                // leg_other^2 + leg_p^2 = hyp^2
                let l1 = get_len(env, &leg_other)
                    .map(|n| n * n)
                    .or_else(|| get_sq(env, &leg_other));
                let l2 = get_len(env, &leg_p)
                    .map(|n| n * n)
                    .or_else(|| get_sq(env, &leg_p));
                let h = get_len(env, &hyp)
                    .map(|n| n * n)
                    .or_else(|| get_sq(env, &hyp));
                match (l1, l2, h) {
                    (Some(a), Some(b), _) => record_sq(
                        env,
                        &hyp,
                        a + b,
                        "pythagoras",
                        vec![Claim::sq_eq(&leg_other, a), Claim::sq_eq(&leg_p, b)],
                    ),
                    (Some(a), _, Some(c)) if c > a => record_sq(
                        env,
                        &leg_p,
                        c - a,
                        "pythagoras",
                        vec![Claim::sq_eq(&leg_other, a), Claim::sq_eq(&hyp, c)],
                    ),
                    (_, Some(b), Some(c)) if c > b => record_sq(
                        env,
                        &leg_other,
                        c - b,
                        "pythagoras",
                        vec![Claim::sq_eq(&leg_p, b), Claim::sq_eq(&hyp, c)],
                    ),
                    _ => {}
                }
            }
        }
    }
}

/// Resolve a ratio expression to a reduced fraction given known lengths.
fn resolve_ratio(e: &RatioExpr, env: &NumericEnv) -> Option<(u32, u32)> {
    match e {
        RatioExpr::Seg(s) => {
            let n = get_len(env, s)?;
            Some((n, 1))
        }
        RatioExpr::Quot { num, den } => {
            let n = match num {
                RatioAtom::Seg(s) => get_len(env, s)?,
                RatioAtom::Int(k) => *k,
            };
            let d = match den {
                RatioAtom::Seg(s) => get_len(env, s)?,
                RatioAtom::Int(k) => *k,
            };
            if d == 0 {
                return None;
            }
            let g = gcd(n, d);
            Some((n / g, d / g))
        }
    }
}

/// Try to derive a concrete length for `seg`.
pub fn solve_len(seg: &str, facts: &FactStore) -> Option<u32> {
    let env = compute(facts);
    get_len(&env, seg)
}

/// True if the ratio equality holds numerically, e.g. `AD/DB = AE/EC` when
/// `3/2 = 6/4`.
pub fn ratio_solves(goal: &Claim, facts: &FactStore) -> bool {
    if let Claim::RatioEq(l, r) = goal {
        let env = compute(facts);
        match (resolve_ratio(l, &env), resolve_ratio(r, &env)) {
            (Some(a), Some(b)) => a == b,
            _ => false,
        }
    } else {
        false
    }
}

/// True if the numeric equality goal holds: a length, a squared length, or
/// two equal lengths.
pub fn numeric_solves(goal: &Claim, facts: &FactStore) -> bool {
    match goal {
        Claim::LenEq(seg, n) => solve_len(seg, facts) == Some(*n),
        Claim::SqEq(seg, v) => {
            let env = compute(facts);
            env.sq.get(&Claim::norm_seg(seg)).copied() == Some(*v)
        }
        Claim::SegEq(a, b) => match (solve_len(a, facts), solve_len(b, facts)) {
            (Some(x), Some(y)) => x == y,
            _ => false,
        },
        _ => ratio_solves(goal, facts),
    }
}

/// Build a proof tree that explains a numeric derivation: how `seg` got its
/// length `n` step by step (segment addition, isosceles legs, Pythagoras...).
pub fn numeric_proof(goal: &Claim, facts: &FactStore) -> Option<Proof> {
    let env = compute(facts);
    match goal {
        Claim::LenEq(seg, n) if env.lens.get(&Claim::norm_seg(seg)).copied() == Some(*n) => {
            Some(explain_len(&env, seg, *n))
        }
        Claim::SqEq(seg, v) if env.sq.get(&Claim::norm_seg(seg)).copied() == Some(*v) => {
            Some(explain_sq(&env, seg, *v))
        }
        Claim::SegEq(a, b) => {
            let x = env.lens.get(&Claim::norm_seg(a)).copied();
            let y = env.lens.get(&Claim::norm_seg(b)).copied();
            if let (Some(x), Some(y)) = (x, y) {
                if x == y {
                    let mut p = explain_len(&env, a, x);
                    p.antecedents.push(explain_len(&env, b, y));
                    p.rule = Some("numeric-equality");
                    return Some(p);
                }
            }
            None
        }
        Claim::RatioEq(_, _) => ratio_proof(goal, &env),
        _ => None,
    }
}

fn explain_len(env: &NumericEnv, seg: &str, n: u32) -> Proof {
    let mut path = Vec::new();
    explain_len_d(env, seg, n, &mut path)
}

fn explain_sq(env: &NumericEnv, seg: &str, v: u32) -> Proof {
    let mut path = Vec::new();
    explain_sq_d(env, seg, v, &mut path)
}

const EXPLAIN_LIMIT: usize = 64;

/// True if `key` is already being explained on the current path, i.e. the
/// derivation would be circular. We truncate rather than recurse so the proof
/// tree can never blow up exponentially.
fn guard(seg: &str, key: &str, path: &mut Vec<String>) -> Option<Proof> {
    if path.len() > EXPLAIN_LIMIT || path.iter().any(|k| k == key) {
        Some(Proof {
            claim: Claim::len_eq(seg, 0),
            antecedents: Vec::new(),
            rule: Some("..."),
        })
    } else {
        None
    }
}

fn explain_len_d(env: &NumericEnv, seg: &str, n: u32, path: &mut Vec<String>) -> Proof {
    let k = Claim::norm_seg(seg);
    if let Some(p) = guard(seg, &format!("L:{k}"), path) {
        return p;
    }
    path.push(format!("L:{k}"));
    let out = match env.len_steps.get(&k) {
        Some(step) if step.rule == "given" => Proof {
            claim: Claim::len_eq(seg, n),
            antecedents: Vec::new(),
            rule: None,
        },
        Some(step) => Proof {
            claim: Claim::len_eq(seg, n),
            rule: Some(step.rule),
            antecedents: step
                .inputs
                .iter()
                .map(|c| explain_d(env, c, path))
                .collect(),
        },
        None => {
            // A length can also be the square root of a derived square, e.g.
            // `BC = sqrt(BC^2)` where `BC^2` came from Pythagoras.
            if env.sq_steps.contains_key(&k) {
                if let Some(s) = env.sq.get(&k).copied() {
                    if isqrt(s) == Some(n) {
                        Proof {
                            claim: Claim::len_eq(seg, n),
                            rule: Some("sqrt"),
                            antecedents: vec![explain_sq_d(env, seg, s, path)],
                        }
                    } else {
                        Proof {
                            claim: Claim::len_eq(seg, n),
                            antecedents: Vec::new(),
                            rule: None,
                        }
                    }
                } else {
                    Proof {
                        claim: Claim::len_eq(seg, n),
                        antecedents: Vec::new(),
                        rule: None,
                    }
                }
            } else {
                Proof {
                    claim: Claim::len_eq(seg, n),
                    antecedents: Vec::new(),
                    rule: None,
                }
            }
        }
    };
    path.pop();
    out
}

fn explain_sq_d(env: &NumericEnv, seg: &str, v: u32, path: &mut Vec<String>) -> Proof {
    let k = Claim::norm_seg(seg);
    let key = format!("S:{k}");
    if path.iter().any(|p| p == &key) || path.len() > EXPLAIN_LIMIT {
        return Proof {
            claim: Claim::sq_eq(seg, v),
            antecedents: Vec::new(),
            rule: Some("..."),
        };
    }
    path.push(key);
    let out = match env.sq_steps.get(&k) {
        Some(step) => Proof {
            claim: Claim::sq_eq(seg, v),
            rule: Some(step.rule),
            antecedents: step
                .inputs
                .iter()
                .map(|c| explain_d(env, c, path))
                .collect(),
        },
        None => {
            // The square is implied by the length itself.
            if let Some(r) = isqrt(v) {
                Proof {
                    claim: Claim::sq_eq(seg, v),
                    rule: Some("square"),
                    antecedents: vec![explain_len_d(env, seg, r, path)],
                }
            } else {
                Proof {
                    claim: Claim::sq_eq(seg, v),
                    antecedents: Vec::new(),
                    rule: None,
                }
            }
        }
    };
    path.pop();
    out
}

fn explain_d(env: &NumericEnv, c: &Claim, path: &mut Vec<String>) -> Proof {
    match c {
        Claim::LenEq(seg, n) => explain_len_d(env, seg, *n, path),
        Claim::SqEq(seg, v) => explain_sq_d(env, seg, *v, path),
        _ => Proof {
            claim: c.clone(),
            antecedents: Vec::new(),
            rule: None,
        },
    }
}

fn ratio_proof(goal: &Claim, env: &NumericEnv) -> Option<Proof> {
    if let Claim::RatioEq(l, r) = goal {
        if resolve_ratio(l, env).is_some() && resolve_ratio(r, env).is_some() {
            let (a, b) = (resolve_ratio(l, env)?, resolve_ratio(r, env)?);
            if a != b {
                return None;
            }
            let mut antecedents = ratio_inputs(l, env);
            antecedents.extend(ratio_inputs(r, env));
            return Some(Proof {
                claim: goal.clone(),
                rule: Some("numeric"),
                antecedents,
            });
        }
    }
    None
}

/// The length facts that establish a ratio expression.
fn ratio_inputs(e: &RatioExpr, env: &NumericEnv) -> Vec<Proof> {
    let mut out = Vec::new();
    match e {
        RatioExpr::Seg(s) => {
            if let Some(n) = get_len(env, s) {
                out.push(explain_len(env, s, n));
            }
        }
        RatioExpr::Quot { num, den } => {
            for atom in [num, den] {
                if let RatioAtom::Seg(s) = atom {
                    if let Some(n) = get_len(env, s) {
                        out.push(explain_len(env, s, n));
                    }
                }
            }
        }
    }
    out
}