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

use crate::claim::{Claim, RatioAtom, RatioExpr, Value};
use crate::checker::{split_seg, FactStore};
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

/// Two numeric facts (or derivations) assigned different lengths to the same
/// segment. The solver keeps the first value it saw and records the conflict
/// rather than silently overwriting it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LenConflict {
    pub seg: String,
    pub old: u32,
    pub new: u32,
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
    /// Contradictory assignments detected while solving. The solver keeps the
    /// first value and records the contradiction here instead of silently
    /// choosing whichever fact was processed last.
    pub conflicts: Vec<LenConflict>,
}

impl NumericEnv {
    pub fn conflicts(&self) -> &[LenConflict] {
        &self.conflicts
    }
}

fn gcd(mut a: u32, mut b: u32) -> u32 {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a.max(1)
}

/// Integer square root via `u64` so the intermediate `r * r` cannot overflow.
fn isqrt(n: u32) -> Option<u32> {
    let v = n as u64;
    let r = (v as f64).sqrt() as u64;
    if r * r == v {
        Some(r as u32)
    } else if (r + 1) * (r + 1) == v {
        Some((r + 1) as u32)
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
    Claim::seg_key(&a.to_string(), &b.to_string())
}

fn record_len(env: &mut NumericEnv, seg: &str, n: u32, rule: &'static str, inputs: Vec<Claim>) {
    let s = Claim::norm_seg(seg);
    if let Some(old) = env.lens.get(&s).copied() {
        if old != n {
            env.conflicts.push(LenConflict {
                seg: s,
                old,
                new: n,
            });
        }
        // Keep the first value and its derivation; never silently overwrite.
        return;
    }
    env.lens.insert(s.clone(), n);
    if let Some(sq) = n.checked_mul(n) {
        env.sq.insert(s.clone(), sq);
    }
    env.len_steps.insert(s, NumStep { rule, inputs });
}

fn record_sq(env: &mut NumericEnv, seg: &str, v: u32, rule: &'static str, inputs: Vec<Claim>) {
    let s = Claim::norm_seg(seg);
    let had_len = env.lens.get(&s).is_some();
    match env.sq.get(&s).copied() {
        Some(old) if old != v => {
            env.conflicts.push(LenConflict {
                seg: s,
                old,
                new: v,
            });
            return;
        }
        Some(_) => {}
        None => {
            env.sq.insert(s.clone(), v);
            if !had_len {
                env.sq_steps
                    .entry(s.clone())
                    .or_insert(NumStep { rule, inputs });
            }
        }
    }
    if let Some(r) = isqrt(v) {
        if let Some(old) = env.lens.get(&s).copied() {
            if old != r {
                env.conflicts.push(LenConflict {
                    seg: s,
                    old,
                    new: r,
                });
            }
        } else {
            env.lens.insert(s, r);
        }
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
            if let Some(old) = env.lens.get(&s).copied() {
                if old != n {
                    env.conflicts.push(LenConflict {
                        seg: s,
                        old,
                        new: n,
                    });
                }
                continue;
            }
            env.lens.insert(s.clone(), n);
            if let Some(sq) = n.checked_mul(n) {
                env.sq.insert(s.clone(), sq);
            }
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
    // Points lying on each line, including the segment endpoints. Any of the
    // three incidence kinds implies the point is on the infinite line.
    let mut on: HashMap<String, Vec<char>> = HashMap::new();
    for c in &claims {
        if let Claim::On(p, s) | Claim::OnSegment(p, s) | Claim::OnLine(p, s) = c {
            if let Some((a, b)) = norm_pts(&s) {
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

fn propagate(env: &mut NumericEnv, claims: &[Claim], on: &HashMap<String, Vec<char>>) {
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
    // (or difference) of the two sub-segments. Only *finite-segment*
    // incidence is used: a point on the infinite line (e.g. a reflection on
    // the extension of a segment) does not lie within the segment, so
    // treating it as an interior point could derive a false length.
    for c in claims {
        if let Claim::OnSegment(p, s) = c {
            if let Some((a, b)) = norm_pts(s) {
                let ab = seg_of(a, b);
                let pch = Claim::norm_ref(p).chars().next().unwrap_or('\0');
                if pch != a && pch != b {
                    let ap = seg_of(a, pch);
                    let pb = seg_of(pch, b);
                    match (get_len(env, &ap), get_len(env, &pb)) {
                        (Some(x), Some(y)) => {
                            if let Some(sum) = x.checked_add(y) {
                                record_len(
                                    env,
                                    &ab,
                                    sum,
                                    "segment-addition",
                                    vec![Claim::len_eq(&ap, x), Claim::len_eq(&pb, y)],
                                );
                            }
                        }
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
                    .and_then(|n| n.checked_mul(n))
                    .or_else(|| get_sq(env, &leg_other));
                let l2 = get_len(env, &leg_p)
                    .and_then(|n| n.checked_mul(n))
                    .or_else(|| get_sq(env, &leg_p));
                let h = get_len(env, &hyp)
                    .and_then(|n| n.checked_mul(n))
                    .or_else(|| get_sq(env, &hyp));
                match (l1, l2, h) {
                    (Some(a), Some(b), _) => {
                        if let Some(sq) = a.checked_add(b) {
                            record_sq(
                                env,
                                &hyp,
                                sq,
                                "pythagoras",
                                vec![Claim::sq_eq(&leg_other, a), Claim::sq_eq(&leg_p, b)],
                            );
                        }
                    }
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

/// Try to resolve a ratio using coordinate arithmetic from midpoint facts.
fn resolve_ratio_coords(e: &RatioExpr, facts: &FactStore) -> Option<(u32, u32)> {
    let mut coords = LineCoords::default();
    derive_ratios_from_midpoints(facts, &mut coords);
    // Debug
    // eprintln!("Coords for {:?}: lines={}", e, coords.coords.len());
    // for (line, pts) in &coords.coords {
    //     eprintln!("  {}: {:?}", line, pts);
    // }
    eval_ratio(e, &coords).map(|(n, d)| (n as u32, d as u32))
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
        // First try numeric lengths
        if let (Some(a), Some(b)) = (resolve_ratio(l, &env), resolve_ratio(r, &env)) {
            if a == b {
                return true;
            }
        }
        // Then try coordinate arithmetic from midpoint facts
        if let (Some(a), Some(b)) = (resolve_ratio_coords(l, facts), resolve_ratio_coords(r, facts)) {
            if a == b {
                return true;
            }
        }
        false
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
        Claim::RatioEq(_, _) => ratio_proof(goal, &env, facts),
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
///
/// The returned node is an explicit truncation marker, not a real derivation:
/// it must not fabricate a numeric fact (`seg=0` would be a false claim).
fn guard(seg: &str, key: &str, path: &mut Vec<String>, target: u32) -> Option<Proof> {
    if path.len() > EXPLAIN_LIMIT || path.iter().any(|k| k == key) {
        Some(Proof {
            claim: Claim::len_eq(seg, target),
            antecedents: Vec::new(),
            rule: Some("[circular derivation truncated]"),
        })
    } else {
        None
    }
}

fn explain_len_d(env: &NumericEnv, seg: &str, n: u32, path: &mut Vec<String>) -> Proof {
    let k = Claim::norm_seg(seg);
    if let Some(p) = guard(seg, &format!("L:{k}"), path, n) {
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
            rule: Some("[circular derivation truncated]"),
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

fn ratio_proof(goal: &Claim, env: &NumericEnv, facts: &FactStore) -> Option<Proof> {
    if let Claim::RatioEq(l, r) = goal {
        // Try numeric lengths first
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
        // Try coordinate arithmetic from midpoint facts
        if let (Some(a), Some(b)) = (resolve_ratio_coords(l, facts), resolve_ratio_coords(r, facts)) {
            if a == b {
                return Some(Proof {
                    claim: goal.clone(),
                    rule: Some("coordinate-arithmetic"),
                    antecedents: Vec::new(),
                });
            }
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

/// Rational number with arbitrary precision (using i64).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Rational {
    num: i64,
    den: i64,
}

impl Rational {
    fn new(num: i64, den: i64) -> Self {
        if den == 0 {
            return Self { num: 0, den: 1 };
        }
        let mut r = Self { num, den };
        r.normalize();
        r
    }

    fn normalize(&mut self) {
        if self.den < 0 {
            self.num = -self.num;
            self.den = -self.den;
        }
        let g = gcd_i64(self.num.abs(), self.den.abs());
        self.num /= g;
        self.den /= g;
    }

    fn add(self, other: Self) -> Self {
        Self::new(self.num * other.den + other.num * self.den, self.den * other.den)
    }

    fn sub(self, other: Self) -> Self {
        Self::new(self.num * other.den - other.num * self.den, self.den * other.den)
    }

    fn mul(self, other: Self) -> Self {
        Self::new(self.num * other.num, self.den * other.den)
    }

    fn div(self, other: Self) -> Self {
        Self::new(self.num * other.den, self.den * other.num)
    }

    fn half(self) -> Self {
        Self::new(self.num, self.den * 2)
    }

    fn to_ratio_atom(self) -> (i64, i64) {
        (self.num, self.den)
    }
}

fn gcd_i64(mut a: i64, mut b: i64) -> i64 {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a.max(1)
}

/// Tracks point coordinates on lines using rational arithmetic.
/// Each line is identified by its normalized segment (e.g., "a-b").
/// Points on the line get rational coordinates where endpoints are 0 and 1.
#[derive(Debug, Default)]
pub struct LineCoords {
    /// line_key -> (point_name -> coordinate)
    pub coords: HashMap<String, HashMap<String, Rational>>,
    /// Tracks which point is at coordinate 0 and 1 for each line
    pub endpoints: HashMap<String, (String, String)>,
}

impl LineCoords {
    fn set_endpoints(&mut self, line: &str, a: &str, b: &str) {
        self.endpoints.insert(line.to_string(), (a.to_string(), b.to_string()));
        let entry = self.coords.entry(line.to_string()).or_default();
        entry.insert(a.to_string(), Rational::new(0, 1));
        entry.insert(b.to_string(), Rational::new(1, 1));
    }

    fn get_coord(&self, line: &str, point: &str) -> Option<Rational> {
        self.coords.get(line)?.get(point).copied()
    }

    fn set_coord(&mut self, line: &str, point: &str, coord: Rational) {
        self.coords.entry(line.to_string()).or_default().insert(point.to_string(), coord);
    }

    /// Set point as midpoint of two other points on the same line.
    fn set_midpoint(&mut self, line: &str, mid: &str, a: &str, b: &str) -> Option<()> {
        let ca = self.get_coord(line, a)?;
        let cb = self.get_coord(line, b)?;
        let cm = ca.add(cb).half();
        self.set_coord(line, mid, cm);
        Some(())
    }

    /// Compute ratio AD/DB for points on a line.
    fn ratio(&self, line: &str, a: &str, d: &str, b: &str) -> Option<(i64, i64)> {
        let ca = self.get_coord(line, a)?;
        let cd = self.get_coord(line, d)?;
        let cb = self.get_coord(line, b)?;
        let ad = cd.sub(ca);
        let db = cb.sub(cd);
        if db.num == 0 {
            return None;
        }
        Some(ad.div(db).to_ratio_atom())
    }
}

/// Derive ratios from On facts and midpoint facts using coordinate arithmetic.
///
/// Collinear segments are first unified into *maximal* lines: a segment is
/// dropped as a coordinate line when both of its endpoints lie on some other
/// segment. This makes nested midpoint chains (`D = Midpoint(AB)`,
/// `E = Midpoint(AD)`, `F = Midpoint(DE)`, ...) share the coordinate system
/// of `AB`, so every level of nesting resolves in one line frame.
pub fn derive_ratios_from_midpoints(facts: &FactStore, coords: &mut LineCoords) {
    use std::collections::HashMap as Map;

    // Collect segments and their On points.
    let mut segs: Vec<(String, String, String)> = Vec::new(); // (key, p, q)
    let mut on_points: Map<String, Vec<String>> = Map::new();
    for c in facts.all() {
        if let Claim::On(p, seg) = c {
            let seg_key = Claim::norm_seg(&seg);
            if let Some((a, b)) = split_seg(&seg_key) {
                if !segs.iter().any(|(k, _, _)| k == &seg_key) {
                    segs.push((seg_key.clone(), a.clone(), b.clone()));
                }
                let entry = on_points.entry(seg_key.clone()).or_default();
                if !entry.contains(&p) {
                    entry.push(p.clone());
                }
            }
        }
    }

    // Keep only maximal segments: drop S when some other T contains both
    // endpoints of S among its points.
    let mut maximal: Vec<(String, String, String)> = Vec::new();
    for (skey, sa, sb) in &segs {
        let dominated = segs.iter().any(|(tkey, _, _)| {
            skey != tkey
                && on_points
                    .get(tkey)
                    .map(|pts| pts.contains(sa) && pts.contains(sb))
                    .unwrap_or(false)
        });
        if !dominated {
            maximal.push((skey.clone(), sa.clone(), sb.clone()));
        }
    }

    // Set up coordinate frames for maximal lines only.
    for (skey, a, b) in &maximal {
        coords.set_endpoints(skey, a, b);
    }

    // Process midpoint facts to derive coordinates (to fixpoint).
    let mut changed = true;
    let mut iteration = 0;
    while changed && iteration < 100 {
        changed = false;
        for c in facts.all() {
            if let Claim::PredVal { name, args, value } = c {
                if name == "ismedian" && value == Value::Bool(true) && args.len() == 2 {
                    let mid = &args[0];
                    let seg = &args[1];
                    if let Some((a, b)) = split_seg(&seg) {
                        // Find the line that contains both endpoints
                        let line_opt = {
                            let mut found = None;
                            for (line, _endpoints) in &coords.endpoints {
                                let ca = coords.get_coord(line, &a);
                                let cb = coords.get_coord(line, &b);
                                if ca.is_some() && cb.is_some() {
                                    found = Some(line.clone());
                                    break;
                                }
                            }
                            found
                        };
                        if let Some(line) = line_opt {
                            let mid_coord = coords.get_coord(&line, mid);
                            if mid_coord.is_none() {
                                coords.set_midpoint(&line, mid, &a, &b);
                                changed = true;
                            }
                        }
                    }
                }
            }
        }
        iteration += 1;
    }
}

/// Try to derive a ratio equality from coordinate arithmetic.
fn try_derive_ratio(facts: &FactStore, goal: &Claim) -> Option<Claim> {
    if let Claim::RatioEq(l, r) = goal {
        // Try to derive both sides
        let mut coords = LineCoords::default();
        derive_ratios_from_midpoints(facts, &mut coords);
        let l_val = eval_ratio(&l, &coords);
        let r_val = eval_ratio(&r, &coords);
        if let (Some(lv), Some(rv)) = (l_val, r_val) {
            if lv == rv {
                return Some(goal.clone());
            }
        }
    }
    None
}

/// Try to resolve a ratio using coordinate arithmetic from midpoint facts.
pub fn eval_ratio(e: &RatioExpr, coords: &LineCoords) -> Option<(i64, i64)> {
    match e {
        RatioExpr::Seg(_s) => {
            // A segment on a line with endpoints 0 and 1 has length 1
            Some((1, 1))
        }
        RatioExpr::Quot { num, den } => {
            // Find the common line for the entire ratio
            let line = find_line_for_ratio(num, den, coords)?;
            // Evaluate both on the same line
            let n = eval_atom_on_line(num, coords, &line)?;
            let d = eval_atom_on_line(den, coords, &line)?;
            if d.0 == 0 {
                return None;
            }
            Some((n.0 * d.1, n.1 * d.0))
        }
    }
}

/// Find the line that contains all points in the ratio expression.
fn find_line_for_ratio(num: &RatioAtom, den: &RatioAtom, coords: &LineCoords) -> Option<String> {
    // Collect all points in the ratio
    let mut points = Vec::new();
    collect_points_from_atom(num, &mut points);
    collect_points_from_atom(den, &mut points);
    
    // Find a line that contains all points
    for (line, _endpoints) in &coords.endpoints {
        let mut all_on_line = true;
        for p in &points {
            if coords.get_coord(line, p).is_none() {
                all_on_line = false;
                break;
            }
        }
        if all_on_line {
            return Some(line.clone());
        }
    }
    None
}

fn collect_points_from_atom(atom: &RatioAtom, points: &mut Vec<String>) {
    match atom {
        RatioAtom::Int(_) => {}
        RatioAtom::Seg(s) => {
            if s.contains('-') {
                let parts: Vec<&str> = s.split('-').collect();
                if parts.len() == 2 {
                    points.push(parts[0].to_string());
                    points.push(parts[1].to_string());
                }
            } else {
                let chars: Vec<char> = s.chars().collect();
                if chars.len() == 2 {
                    points.push(chars[0].to_string());
                    points.push(chars[1].to_string());
                }
            }
        }
    }
}

/// Evaluate a ratio atom on a specific line.
fn eval_atom_on_line(a: &RatioAtom, coords: &LineCoords, line: &str) -> Option<(i64, i64)> {
    match a {
        RatioAtom::Int(n) => Some((*n as i64, 1)),
        RatioAtom::Seg(s) => {
            let (a, b) = if s.contains('-') {
                let parts: Vec<&str> = s.split('-').collect();
                if parts.len() == 2 {
                    (parts[0].to_string(), parts[1].to_string())
                } else {
                    return None;
                }
            } else {
                let chars: Vec<char> = s.chars().collect();
                if chars.len() == 2 {
                    (chars[0].to_string(), chars[1].to_string())
                } else {
                    return None;
                }
            };
            
            let ca = coords.get_coord(line, &a)?;
            let cb = coords.get_coord(line, &b)?;
            let len_num = (cb.num * ca.den - ca.num * cb.den).abs();
            let len_den = ca.den * cb.den;
            Some((len_num, len_den))
        }
    }
}

/// Evaluate a ratio atom using coordinate arithmetic.
pub fn eval_atom(a: &RatioAtom, coords: &LineCoords) -> Option<(i64, i64)> {
    match a {
        RatioAtom::Int(n) => Some((*n as i64, 1)),
        RatioAtom::Seg(s) => {
            // Parse segment endpoints
            let (a, b) = if s.contains('-') {
                let parts: Vec<&str> = s.split('-').collect();
                if parts.len() == 2 {
                    (parts[0].to_string(), parts[1].to_string())
                } else {
                    return None;
                }
            } else {
                let chars: Vec<char> = s.chars().collect();
                if chars.len() == 2 {
                    (chars[0].to_string(), chars[1].to_string())
                } else {
                    return None;
                }
            };

            // Find a line that contains both endpoints
            for (line, _endpoints) in &coords.endpoints {
                let ca = coords.get_coord(line, &a);
                let cb = coords.get_coord(line, &b);
                if let (Some(ca), Some(cb)) = (ca, cb) {
                    // Both points are on this line
                    // Segment length = |cb - ca| as rational
                    let len_num = (cb.num * ca.den - ca.num * cb.den).abs();
                    let len_den = ca.den * cb.den;
                    return Some((len_num, len_den));
                }
            }
            None
        }
    }
}
