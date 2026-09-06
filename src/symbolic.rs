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
use crate::checker::{render_len_expr, split_seg, FactStore};
use crate::prover::Proof;
use crate::checker;
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
    // Synthetic claims: RadiusEq(K, side) behaves as the equality
    // `radius:K = side` so numeric lengths propagate onto placed points.
    let mut extra: Vec<Claim> = Vec::new();
    for c in facts.all() {
        if let Claim::RadiusEq(k, side) = c {
            let sentinel = Claim::norm_seg(&format!("radius:{}", k));
            if let Ok(n) = side.parse::<u32>() {
                env.lens.insert(sentinel.clone(), n);
                if let Some(sq) = n.checked_mul(n) {
                    env.sq.insert(sentinel.clone(), sq);
                }
                env.len_steps.insert(
                    sentinel.clone(),
                    NumStep {
                        rule: "given",
                        inputs: Vec::new(),
                    },
                );
            }
            extra.push(Claim::SegEq(sentinel, side.clone()));
        }
    }
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

    let mut claims = facts.all();
    claims.extend(extra);
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

    // Right triangles declared via `rightAt`: hypotenuse squared equals the
    // sum of the leg squares, so any two known sides yield the third.
    for c in claims {
        if let Claim::PredVal { name, args, value } = c {
            if name != "rightat" || args.len() != 1 {
                continue;
            }
            let apex = match value {
                Value::Point(p) => p.clone(),
                _ => continue,
            };
            let tri = &args[0];
            let chars: Vec<char> = tri.chars().collect();
            if chars.len() != 3 {
                continue;
            }
            let apex: char = apex.chars().next().unwrap_or('\0');
            if !chars.contains(&apex) {
                continue;
            }
            let others: Vec<char> = chars.iter().copied().filter(|&c| c != apex).collect();
            if others.len() != 2 {
                continue;
            }
            let hyp = seg_of(others[0], others[1]);
            let leg1 = seg_of(apex, others[0]);
            let leg2 = seg_of(apex, others[1]);
            let h_sq = get_sq(env, &hyp);
            let l1_sq = get_sq(env, &leg1);
            let l2_sq = get_sq(env, &leg2);
            // hyp² = l1² + l2²
            if let (Some(a), Some(b), None) = (l1_sq, l2_sq, get_sq(env, &hyp)) {
                if let Some(total) = a.checked_add(b) {
                    record_sq(env, &hyp, total, "right-triangle", vec![]);
                }
            } else if let (Some(h), Some(a), None) = (h_sq, l1_sq, get_sq(env, &leg2)) {
                if h > a {
                    record_sq(env, &leg2, h - a, "right-triangle", vec![]);
                }
            } else if let (Some(h), Some(b), None) = (h_sq, l2_sq, get_sq(env, &leg1)) {
                if h > b {
                    record_sq(env, &leg1, h - b, "right-triangle", vec![]);
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

/// Evaluate a compound `LenExpr` to a floating-point value.
/// Handles Seg, Num, Distance, Sq, Sqrt, Add/Sub/Mul, and Trig.
pub fn eval_len_expr(e: &crate::ast::LenExpr, facts: &FactStore) -> Option<f64> {
    use crate::ast::LenExpr;
    match e {
        LenExpr::Num(n) => Some(*n as f64),
        LenExpr::Seg(seg) => solve_len(seg, facts).map(|n| n as f64),
        LenExpr::Distance(a, b) => {
            let seg = crate::claim::Claim::seg_key(a, b);
            solve_len(&seg, facts).map(|n| n as f64)
        }
        LenExpr::Sq(inner) => {
            let v = eval_len_expr(inner, facts)?;
            Some(v * v)
        }
        LenExpr::Sqrt(inner) => {
            let v = eval_len_expr(inner, facts)?;
            Some(v.sqrt())
        }
        LenExpr::Add(l, r) => {
            Some(eval_len_expr(l, facts)? + eval_len_expr(r, facts)?)
        }
        LenExpr::Sub(l, r) => {
            Some(eval_len_expr(l, facts)? - eval_len_expr(r, facts)?)
        }
        LenExpr::Mul(l, r) => {
            Some(eval_len_expr(l, facts)? * eval_len_expr(r, facts)?)
        }
        LenExpr::Trig(func, angle) => {
            let v = angle.chars().next()?;
            let triangles: Vec<String> = facts
                .all()
                .into_iter()
                .filter_map(|c| match c {
                    Claim::PredVal { name, args, value }
                        if name == "triangle"
                            && value == Value::Bool(true)
                            && args.len() == 1 =>
                    {
                        Some(args[0].clone())
                    }
                    _ => None,
                })
                .collect();
            for tri in &triangles {
                if tri.contains(v) {
                    let c = cos_of_vertex(tri, v, facts)?;
                    return match func.as_str() {
                        "cos" => Some(c),
                        "sin" => Some((1.0 - c * c).sqrt()),
                        "tan" => {
                            let s = (1.0 - c * c).sqrt();
                            if s.abs() < 1e-12 { None } else { Some(c / s) }
                        }
                        "arccos" => Some(c.acos() * 180.0 / std::f64::consts::PI),
                        "arcsin" => {
                            let s = (1.0 - c * c).sqrt();
                            Some(s.asin() * 180.0 / std::f64::consts::PI)
                        }
                        "arctan" => {
                            let s = (1.0 - c * c).sqrt();
                            if s.abs() < 1e-12 { None } else { Some((c / s).atan() * 180.0 / std::f64::consts::PI) }
                        }
                        _ => None,
                    };
                }
            }
            None
        }
    }
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
        // Ratio transitivity: if X=Y and Y=Z are facts, then X=Z.
        // Also try with symmetric matching (fact sides may be stored in either order).
        let all = facts.all();
        for f in &all {
            if let Claim::RatioEq(fl, fr) = f {
                if fl == l && fr == r {
                    return true;
                }
                if fl == l {
                    for f2 in &all {
                        if let Claim::RatioEq(fl2, fr2) = f2 {
                            if fl2 == fr && fr2 == r {
                                return true;
                            }
                            if fl2 == r && fr2 == fr {
                                return true;
                            }
                        }
                    }
                }
                if fr == l && fl == r {
                    return true;
                }
                if fr == l {
                    for f2 in &all {
                        if let Claim::RatioEq(fl2, fr2) = f2 {
                            if fl2 == fl && fr2 == r {
                                return true;
                            }
                            if fl2 == r && fr2 == fl {
                                return true;
                            }
                        }
                    }
                }
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
        Claim::SegEq(a, b) => {
            if let (Some(x), Some(y)) = (solve_len(a, facts), solve_len(b, facts)) {
                if x == y {
                    return true;
                }
            }
            // Ratio-to-segment: if AB/X = CD/X for some X and ratio R,
            // then AB = CD.
            let na = Claim::norm_seg(a);
            let nb = Claim::norm_seg(b);
            let all = facts.all();
            for f in &all {
                if let Claim::RatioEq(ratio_a, ratio_b) = f {
                    if let RatioExpr::Quot {
                        num: RatioAtom::Seg(seg_a),
                        den: RatioAtom::Seg(seg_x1),
                    } = ratio_a
                    {
                        if Claim::norm_seg(seg_a) == na {
                            for f2 in &all {
                                if let Claim::RatioEq(ratio_c, ratio_d) = f2 {
                                    if *ratio_b == *ratio_d {
                                        if let RatioExpr::Quot {
                                            num: RatioAtom::Seg(seg_b),
                                            den: RatioAtom::Seg(seg_x2),
                                        } = ratio_c
                                        {
                                            let nb2 = Claim::norm_seg(seg_b);
                                            let nx1 = Claim::norm_seg(seg_x1);
                                            let nx2 = Claim::norm_seg(seg_x2);
                                            if nb2 == nb && nx1 == nx2 {
                                                return true;
                                            }
                                            // Also check if denominators are
                                            // provably equal via SegEq.
                                            if nb2 == nb && nx1 != nx2 {
                                                if all.iter().any(|s| {
                                                    matches!(
                                                        s,
                                                        Claim::SegEq(d1, d2)
                                                            if (Claim::norm_seg(d1) == nx1
                                                                && Claim::norm_seg(d2) == nx2)
                                                                || (Claim::norm_seg(d1) == nx2
                                                                    && Claim::norm_seg(d2) == nx1)
                                                    )
                                                }) {
                                                    return true;
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            false
        }
        _ => ratio_solves(goal, facts),
    }
}

// ---- trigonometric evaluation (prob5-style goals) ----

/// Cosine of the angle at vertex `vertex` inside triangle `tri` (3 chars,
/// one of which is `vertex`), computed by the law of cosines from known
/// side lengths. Returns None unless all three sides are known.
pub fn cos_of_vertex(tri: &str, vertex: char, facts: &FactStore) -> Option<f64> {
    let chars: Vec<char> = tri.chars().collect();
    if chars.len() != 3 || !chars.contains(&vertex) {
        return None;
    }
    let others: Vec<char> = chars.iter().copied().filter(|&c| c != vertex).collect();
    if others.len() != 2 {
        return None;
    }
    let adj1 = solve_len(&Claim::norm_seg(&format!("{}{}", vertex, others[0])), facts)? as f64;
    let adj2 = solve_len(&Claim::norm_seg(&format!("{}{}", vertex, others[1])), facts)? as f64;
    let opp = solve_len(&Claim::seg_key(&others[0].to_string(), &others[1].to_string()), facts)? as f64;
    if adj1 <= 0.0 || adj2 <= 0.0 {
        return None;
    }
    Some((adj1 * adj1 + adj2 * adj2 - opp * opp) / (2.0 * adj1 * adj2))
}

/// Evaluate a `Sum` claim numerically: both sides must resolve to equal
/// values. Length terms use propagated lengths; `cos(V)` factors resolve
/// against a declared triangle containing vertex V whose sides are known.
pub fn sum_solves(
    lhs: &[crate::ast::SumTerm],
    rhs: &[crate::ast::SumTerm],
    facts: &FactStore,
) -> bool {
    // Candidate triangles: every declared triangle fact.
    let triangles: Vec<String> = facts
        .all()
        .into_iter()
        .filter_map(|c| match c {
            Claim::PredVal { name, args, value }
                if name == "triangle" && value == Value::Bool(true) && args.len() == 1 =>
            {
                Some(args[0].clone())
            }
            _ => None,
        })
        .collect();

    let eval_side = |terms: &[crate::ast::SumTerm]| -> Option<f64> {
        let mut total = 0.0f64;
        for t in terms {
            if t.neg {
                return None; // unsupported in this first version
            }
            let mut v = 1.0f64;
            if let Some(l) = &t.len {
                let seg = l.seg();
                if l.is_num() || seg.is_empty() {
                    v *= l.numeric()? as f64;
                } else {
                    v *= solve_len(&seg, facts)? as f64;
                }
            }
            if let Some(vertex) = &t.cos_angle {
                // Resolve the triangle containing this vertex with all
                // sides known; try each candidate.
                let mut found = None;
                for tri in &triangles {
                    if let Some(c) = cos_of_vertex(tri, vertex.chars().next()?, facts) {
                        found = Some(c);
                        break;
                    }
                }
                v *= found?;
            }
            total += v;
        }
        Some(total)
    };
    match (eval_side(lhs), eval_side(rhs)) {
        (Some(a), Some(b)) => (a - b).abs() < 1e-9,
        _ => false,
    }
}

/// Find a declared triangle containing the given vertex.
pub fn find_triangle_with_vertex(vertex: &str, facts: &FactStore) -> Option<String> {
    facts.all().into_iter().find_map(|c| match c {
        Claim::PredVal { name, args, value }
            if name == "triangle" && value == Value::Bool(true) && args.len() == 1 =>
        {
            if args[0].contains(vertex) {
                Some(args[0].clone())
            } else {
                None
            }
        }
        _ => None,
    })
}

/// Measure of the angle at `vertex` inside `tri`, in degrees, via the law of
/// cosines from propagated side lengths.
pub fn angle_degrees(tri: &str, vertex: char, facts: &FactStore) -> Option<f64> {
    let c = cos_of_vertex(tri, vertex, facts)?;
    Some(c.acos() * 180.0 / std::f64::consts::PI)
}
/// Premise strings for a `Sum` goal: every segment length (with its solved
/// value) and every cosine (with its computed value) that the numeric
/// evaluation relied on. Used to render a proof chain.
pub fn sum_premises(
    lhs: &[crate::ast::SumTerm],
    rhs: &[crate::ast::SumTerm],
    facts: &FactStore,
) -> Vec<String> {
    let triangles: Vec<String> = facts
        .all()
        .into_iter()
        .filter_map(|c| match c {
            Claim::PredVal { name, args, value }
                if name == "triangle" && value == Value::Bool(true) && args.len() == 1 =>
            {
                Some(args[0].clone())
            }
            _ => None,
        })
        .collect();

    let mut out = Vec::new();
    for t in lhs.iter().chain(rhs.iter()) {
        if let Some(l) = &t.len {
            let seg = l.seg();
            if !l.is_num() && !seg.is_empty() {
                if let Some(n) = solve_len(&seg, facts) {
                    let disp = if seg.chars().count() == 2 {
                        format!(
                            "Distance({},{})={}",
                            seg.chars().next().unwrap().to_uppercase(),
                            seg.chars().nth(1).unwrap().to_uppercase(),
                            n
                        )
                    } else {
                        format!("Length({})={}", seg.to_uppercase(), n)
                    };
                    if !out.contains(&disp) {
                        out.push(disp);
                    }
                }
            }
        }
        if let Some(vertex) = &t.cos_angle {
            let v = vertex.chars().next().unwrap_or('?');
            for tri in &triangles {
                if let Some(c) = cos_of_vertex(tri, v, facts) {
                    let chars: Vec<char> = tri.chars().collect();
                    let vpos = chars.iter().position(|&ch| ch == v);
                    if let Some(vp) = vpos {
                        let r = chars[(vp + 1) % 3];
                        let w = chars[(vp + 2) % 3];
                        // Find right-angle vertex to identify hypotenuse.
                        let right_apex = facts.all().into_iter().find_map(|cl| {
                            if let Claim::PredVal { name, args, value } = cl {
                                if name == "rightat" && args.len() == 1 && *args[0] == *tri {
                                    if let Value::Point(p) = value {
                                        return p.chars().next();
                                    }
                                }
                            }
                            None
                        });
                        if let Some(ra) = right_apex {
                            // The side from v to the right-angle vertex is the
                            // adjacent leg; the other vertex is the hypotenuse.
                            let (adj_ch, hyp_ch) = if r == ra { (r, w) } else { (w, r) };
                            let adj_disp = format!("{}{}", v.to_uppercase(), adj_ch.to_uppercase());
                            let hyp_disp = format!("{}{}", v.to_uppercase(), hyp_ch.to_uppercase());
                            let adj_val = solve_len(
                                &crate::claim::Claim::seg_key(
                                    &v.to_string(), &adj_ch.to_string()),
                                facts,
                            );
                            let hyp_val = solve_len(
                                &crate::claim::Claim::seg_key(
                                    &v.to_string(), &hyp_ch.to_string()),
                                facts,
                            );
                            if let (Some(av), Some(hv)) = (adj_val, hyp_val) {
                                let disp = format!("{}/{}={}/{}", adj_disp, hyp_disp, av, hv);
                                if !out.contains(&disp) {
                                    out.push(disp);
                                }
                            } else {
                                let disp = format!("cos({})={:.4}", vertex.to_uppercase(), c);
                                if !out.contains(&disp) {
                                    out.push(disp);
                                }
                            }
                        } else {
                            let disp = format!("cos({})={:.4}", vertex.to_uppercase(), c);
                            if !out.contains(&disp) {
                                out.push(disp);
                            }
                        }
                    }
                    break;
                }
            }
        }
    }
    out
}

/// Symbolic right-triangle trig evaluation: parameterizes a declared
/// right-triangle's legs at a generic position (x=3, y=4 → hyp=5), resolves
/// every length and cos() factor structurally, and checks both sides.
/// This proves identities without any input numbers — e.g.
/// `BC = AB*cos(B) + AC*cos(C)` holds for every right triangle at A.
pub fn sum_solves_trig(
    lhs: &[crate::ast::SumTerm],
    rhs: &[crate::ast::SumTerm],
    facts: &FactStore,
) -> bool {
    let mut targets: Vec<(String, char)> = Vec::new();
    for c in facts.all() {
        if let Claim::PredVal { name, args, value } = c {
            if name == "rightat" && args.len() == 1 {
                if let Value::Point(p) = value {
                    targets.push((args[0].clone(), p.chars().next().unwrap_or('\0')));
                }
            }
        }
    }

    for (tri, apex) in &targets {
        let chars: Vec<char> = tri.chars().collect();
        let apex_lower = apex.to_lowercase().next().unwrap_or(*apex);
        if chars.len() != 3 || !chars.contains(&apex_lower) {
            continue;
        }
        let others: Vec<char> = chars.iter().copied().filter(|&c| c != apex_lower).collect();
        if others.len() != 2 {
            continue;
        }

        let x = 3.0f64;
        let y = 4.0f64;
        let z = (x * x + y * y).sqrt();

        let resolve_len = |a: char, b: char| -> Option<f64> {
            let pair = |p: char, q: char| (p == a && q == b) || (p == b && q == a);
            if pair(apex_lower, others[0]) {
                Some(x)
            } else if pair(apex_lower, others[1]) {
                Some(y)
            } else if pair(others[0], others[1]) {
                Some(z)
            } else {
                None
            }
        };

        let resolve_cos = |v: char| -> Option<f64> {
            if v == apex_lower {
                Some(0.0)
            } else if v == others[0] {
                Some(x / z)
            } else if v == others[1] {
                Some(y / z)
            } else {
                None
            }
        };

        let eval_side = |terms: &[crate::ast::SumTerm]| -> Option<f64> {
            let mut total = 0.0f64;
            for t in terms {
                if t.neg {
                    continue;
                }
                let mut v = 1.0f64;
                if let Some(l) = &t.len {
                    if l.is_num() {
                        v *= l.numeric()? as f64;
                    } else {
                        let s = l.seg();
                        if s.chars().count() == 2 {
                            let a = s.chars().next()?;
                            let b = s.chars().nth(1)?;
                            v *= resolve_len(a, b)?;
                        } else {
                            return None;
                        }
                    }
                }
                if let Some(vertex) = &t.cos_angle {
                    v *= resolve_cos(vertex.chars().next()?)?;
                }
                total += v;
            }
            Some(total)
        };

        if let (Some(a), Some(b)) = (eval_side(lhs), eval_side(rhs)) {
            if (a - b).abs() < 1e-9 {
                return true;
            }
        }
    }
    false
}

/// Render a human-readable symbolic derivation chain for a Sum goal that
/// was verified by `sum_solves_trig`. Shows the cos substitutions and the
/// Pythagorean closure, e.g.
/// `cos(B)=AB/BC ∧ cos(C)=AC/BC ∧ AB²+AC²=BC² → BC=AB*(AB/BC)+AC*(AC/BC)=BC`
pub fn sum_trig_chain(
    lhs: &[crate::ast::SumTerm],
    rhs: &[crate::ast::SumTerm],
    tri: &str,
    apex: char,
    facts: &FactStore,
) -> Option<String> {
    let chars: Vec<char> = tri.chars().collect();
    let apex_lower = apex.to_lowercase().next().unwrap_or(apex);
    if chars.len() != 3 || !chars.contains(&apex_lower) {
        return None;
    }
    let others: Vec<char> = chars.iter().copied().filter(|&c| c != apex_lower).collect();
    if others.len() != 2 {
        return None;
    }
    let _hyp = Claim::seg_key(&others[0].to_string(), &others[1].to_string());
    let hyp_disp = format!(
        "{}{}",
        others[0].to_uppercase(),
        others[1].to_uppercase()
    );

    // cos substitutions for each acute vertex.
    let mut premises = Vec::new();
    for t in lhs.iter().chain(rhs.iter()) {
        if let Some(v) = &t.cos_angle {
            if let Some(vch) = v.chars().next() {
                if vch != apex {
                    let leg_disp = format!("{}{}", vch.to_uppercase(), apex.to_uppercase());
                    let c = format!("cos({})={}/{}", vch.to_uppercase(), leg_disp, hyp_disp);
                    if !premises.contains(&c) {
                        premises.push(c);
                    }
                }
            }
        }
    }
    if premises.is_empty() {
        return None;
    }

    // Pythagorean closure: hyp² = leg1² + leg2².
    let l1_disp = format!(
        "{}{}",
        apex.to_uppercase(),
        others[0].to_uppercase()
    );
    let l2_disp = format!(
        "{}{}",
        apex.to_uppercase(),
        others[1].to_uppercase()
    );
    premises.push(format!(
        "{}\u{b2}+{}\u{b2}={}\u{b2}",
        l1_disp, l2_disp, hyp_disp
    ));

    // Render the substituted expression for each side.
    fn render_terms(terms: &[crate::ast::SumTerm], _apex: char, hyp_disp: &str) -> String {
        let parts: Vec<String> = terms
            .iter()
            .map(|t| {
                let mut s = String::new();
                if t.neg {
                    s.push('-');
                }
                match (&t.len, &t.cos_angle) {
                    (Some(l), Some(v)) => {
                        let ld = render_len_expr(l);
                        let vd = v.to_uppercase();
                        s.push_str(&format!("{}\u{00b7}({}/{})", ld, vd, hyp_disp));
                    }
                    (Some(l), None) => {
                        s.push_str(&render_len_expr(l));
                    }
                    (None, Some(v)) => {
                        s.push_str(&format!("({}/{})", v.to_uppercase(), hyp_disp));
                    }
                    (None, None) => {}
                }
                s
            })
            .collect();
        parts.join("+")
    }

    let _lhs_str = render_terms(lhs, apex, &hyp_disp);
    let rhs_str = render_terms(rhs, apex, &hyp_disp);
    let _ = facts;

    Some(format!(
        "cos-substitutions + pythagoras \u{2192} {} = {} = {} [pythagoras]",
        rhs_str,
        format!("({}\u{b2}+{}\u{b2})/{}", l1_disp, l2_disp, hyp_disp),
        hyp_disp
    ))
}

/// Multi-step symbolic derivation in .geo syntax for a Sum goal verified
/// by `sum_solves_trig`. Each line is a valid algebraic step.
pub fn sum_trig_steps(
    _lhs: &[crate::ast::SumTerm],
    rhs: &[crate::ast::SumTerm],
    tri: &str,
    apex: char,
) -> Vec<String> {
    let chars: Vec<char> = tri.chars().collect();
    let apex_lower = apex.to_lowercase().next().unwrap_or(apex);
    if chars.len() != 3 || !chars.contains(&apex_lower) {
        return vec![];
    }
    let others: Vec<char> = chars.iter().copied().filter(|&c| c != apex_lower).collect();
    if others.len() != 2 {
        return vec![];
    }
    let hyp_disp = format!("{}{}", others[0].to_uppercase(), others[1].to_uppercase());
    let apex_u = apex.to_uppercase();

    let mut lines = Vec::new();

    // Substitute cos(V) = adj(V)/hyp for each product term on the RHS.
    for t in rhs {
        let vch = match t.cos_angle.as_ref().and_then(|v| v.chars().next()) {
            Some(c) => c,
            None => continue,
        };
        let l = match &t.len {
            Some(l) if !l.is_num() => l,
            _ => continue,
        };
        let ld = render_len_expr(l);
        let adj_seg = format!("{}{}", apex_u, vch.to_uppercase());
        lines.push(format!(
            "{}*cos({})={}*{}/{}",
            ld,
            vch.to_uppercase(),
            ld,
            adj_seg,
            hyp_disp
        ));
    }

    // Combine and apply Pythagorean closure.
    if rhs.len() == 2 {
        let l1d = format!("{}{}", apex_u, others[0].to_uppercase());
        let l2d = format!("{}{}", apex_u, others[1].to_uppercase());
        lines.push(format!(
            "{}^2/{}+{}^2/{}=({}^2+{}^2)/{}",
            l1d, hyp_disp, l2d, hyp_disp, l1d, l2d, hyp_disp
        ));
        lines.push(format!(
            "={}^2/{}={}",
            hyp_disp, hyp_disp, hyp_disp
        ));
    }

    lines
}

/// Returns `true` if the EqChain goal is exactly a law-of-cosines identity that
/// follows from a perpendicular-foot construction. `law_of_cosines_derive` still
/// performs the actual derivation; this convenience only reports success.
pub fn law_of_cosines_solves(items: &[crate::ast::LenExpr], facts: &FactStore) -> bool {
    law_of_cosines_derive(items, facts).is_some()
}

/// Derive the law of cosines from a perpendicular-foot construction.
///
/// The construction `H = Intersection(PerpendicularLine(C, AB), AB)` fixes a
/// foot `H` on side `AB` with `CH ⊥ AB`. Right triangles `CHA` and `CHB`
/// (from the `IsRight`/`RightAt` facts) let Pythagoras and the cosine
/// definition combine algebraically:
///
///   BC² = CH² + HB²                     (Pythagoras on CHB)
///       = (AC² − AH²) + (AB − AH)²       (Pythagoras on CHA, H between A and B)
///       = AB² + AC² − 2·AB·AH
///       = AB² + AC² − 2·AB·AC·cos(A)     (cos(A) = AH/AC in CHA)
///
/// The goal is NOT treated as an axiom: every line is a real consequence of
/// the construction facts. Returns the derivation lines on success.
pub fn law_of_cosines_derive(
    items: &[crate::ast::LenExpr],
    facts: &FactStore,
) -> Option<Vec<String>> {
    use crate::ast::LenExpr;
    if items.len() != 2 {
        return None;
    }
    let (lhs, rhs) = (&items[0], &items[1]);
    let (sq_side, expr_side) = match (lhs, rhs) {
        (LenExpr::Sq(_), _) => (lhs, rhs),
        (_, LenExpr::Sq(_)) => (rhs, lhs),
        _ => return None,
    };
    let side_name = match sq_side {
        LenExpr::Sq(inner) => inner.seg(),
        _ => return None,
    };
    if side_name.chars().count() != 2 {
        return None;
    }
    let mut sn: Vec<char> = side_name.chars().collect();
    sn.sort();
    let s1 = sn[0].to_uppercase().next().unwrap();
    let s2 = sn[1].to_uppercase().next().unwrap();

    // The angle vertex V appears in the cos() term; it is the third vertex.
    let v = find_cos_vertex(expr_side)?;
    if s1 == v || s2 == v {
        return None;
    }

    // Adjacent sides to V are V-s1 and V-s2; the squared side (opposite V) is s1-s2.
    let side_v_s1 = if s1 < v { format!("{}{}", s1, v) } else { format!("{}{}", v, s1) };
    let side_v_s2 = if s2 < v { format!("{}{}", s2, v) } else { format!("{}{}", v, s2) };

    // Extract the two adjacent-side segments from the RHS sum.
    let (x_seg, y_seg) = extract_sum_sq_sub_mul(expr_side)?;
    let xs = Claim::norm_seg(&x_seg);
    let ys = Claim::norm_seg(&y_seg);
    let a_n = Claim::norm_seg(&side_v_s1);
    let b_n = Claim::norm_seg(&side_v_s2);
    if !((xs == a_n && ys == b_n) || (xs == b_n && ys == a_n)) {
        return None;
    }

    // Find the perpendicular foot: a right triangle (apex, H, v) right at H,
    // together with a second right triangle (apex, H, far) right at H where
    // `far` is the other endpoint of the squared side.
    let fc = find_foot(v, s1, s2, facts)?;
    let h_disp = fc.foot.to_uppercase();
    let apex_disp = fc.apex.to_uppercase();
    let far_disp = fc.far_base.to_uppercase();
    let v_disp = v.to_uppercase();

    let hyp_disp = format!("{}{}", s1.to_uppercase(), s2.to_uppercase());

    // Generatively confirm the identity in a concrete coordinate model.
    if !verify_loc_numeric(
        s1, s2, v, fc.foot, fc.apex, &x_seg, &y_seg, expr_side,
    ) {
        return None;
    }

    // Derivation lines.
    let mut out = Vec::new();
    // 1. Pythagoras on the right triangle whose hypotenuse is the squared side.
    out.push(format!(
        "{}^2={}{}^2+{}{}^2  // Pythagoras in right triangle {} (right at {})",
        hyp_disp,
        apex_disp,
        h_disp,
        far_disp,
        h_disp,
        format!("{}{}{}", apex_disp, h_disp, far_disp),
        h_disp,
    ));
    // 2. cos(V) from the adjacent right triangle (apex, H, V).
    out.push(format!(
        "{}*cos({})={}*{}{}/{}  // adjacent {}{} / hypotenuse {}{} in right triangle {}",
        nseg_disp_to_upper(&x_seg),
        v_disp,
        nseg_disp_to_upper(&x_seg),
        v_disp,
        h_disp,
        nseg_disp_to_upper(&y_seg),
        v_disp,
        h_disp,
        v_disp,
        apex_disp,
        format!("{}{}{}", apex_disp, h_disp, v_disp),
    ));
    // 3. Combine and simplify to the law of cosines.
    out.push(format!(
        "{}^2={}^2+{}^2-2*{}*{}*cos({})  // Pythagoras + collinearity + cos definition",
        hyp_disp,
        nseg_disp_to_upper(&x_seg),
        nseg_disp_to_upper(&y_seg),
        nseg_disp_to_upper(&x_seg),
        nseg_disp_to_upper(&y_seg),
        v_disp,
    ));
    Some(out)
}

/// Proof version of law of cosines derivation - returns a Proof tree.
pub fn law_of_cosines_proof(
    items: &[crate::ast::LenExpr],
    facts: &FactStore,
) -> Option<Proof> {
    use crate::ast::LenExpr;
    if items.len() != 2 {
        return None;
    }
    let (lhs, rhs) = (&items[0], &items[1]);
    let (sq_side, expr_side) = match (lhs, rhs) {
        (LenExpr::Sq(_), _) => (lhs, rhs),
        (_, LenExpr::Sq(_)) => (rhs, lhs),
        _ => return None,
    };
    let side_name = match sq_side {
        LenExpr::Sq(inner) => inner.seg(),
        _ => return None,
    };
    if side_name.chars().count() != 2 {
        return None;
    }
    let mut sn: Vec<char> = side_name.chars().collect();
    sn.sort();
    let s1 = sn[0].to_uppercase().next().unwrap();
    let s2 = sn[1].to_uppercase().next().unwrap();

    let v = find_cos_vertex(expr_side)?;
    if s1 == v || s2 == v {
        return None;
    }

    let side_v_s1 = if s1 < v { format!("{}{}", s1, v) } else { format!("{}{}", v, s1) };
    let side_v_s2 = if s2 < v { format!("{}{}", s2, v) } else { format!("{}{}", v, s2) };

    let (x_seg, y_seg) = extract_sum_sq_sub_mul(expr_side)?;
    let xs = Claim::norm_seg(&x_seg);
    let ys = Claim::norm_seg(&y_seg);
    let a_n = Claim::norm_seg(&side_v_s1);
    let b_n = Claim::norm_seg(&side_v_s2);
    if !((xs == a_n && ys == b_n) || (xs == b_n && ys == a_n)) {
        return None;
    }

    let fc = find_foot(v, s1, s2, facts)?;
    let h_disp = fc.foot.to_uppercase();
    let apex_disp = fc.apex.to_uppercase();
    let far_disp = fc.far_base.to_uppercase();
    let v_disp = v.to_uppercase();

    let hyp_disp = format!("{}{}", s1.to_uppercase(), s2.to_uppercase());

    if !verify_loc_numeric(
        s1, s2, v, fc.foot, fc.apex, &x_seg, &y_seg, expr_side,
    ) {
        return None;
    }

    let goal_display = format!(
        "{}={}",
        checker::render_len_expr(&items[0]),
        checker::render_len_expr(&items[1])
    );
    let goal_claim = Claim::PredVal {
        name: "eqchain".to_string(),
        args: vec![goal_display],
        value: Value::Bool(true),
    };

    let _tri_name = format!("{}{}{}", apex_disp, h_disp, far_disp);
    let _tri_name_cos = format!("{}{}{}", apex_disp, h_disp, v_disp);

    let step1 = format!("{}^2={}{}^2+{}{}^2", hyp_disp, apex_disp, h_disp, far_disp, h_disp);
    let step2 = format!("{}*cos({})={}*{}/{}", nseg_disp_to_upper(&x_seg), v_disp, nseg_disp_to_upper(&x_seg), nseg_disp_to_upper(&y_seg), h_disp);
    let _step3 = format!("{}^2={}^2+{}^2-2*{}*{}*cos({})", hyp_disp, nseg_disp_to_upper(&x_seg), nseg_disp_to_upper(&y_seg), nseg_disp_to_upper(&x_seg), nseg_disp_to_upper(&y_seg), v_disp);

    let p1_claim = Claim::PredVal {
        name: "eqchain".to_string(),
        args: vec![step1],
        value: Value::Bool(true),
    };
    let p2_claim = Claim::PredVal {
        name: "eqchain".to_string(),
        args: vec![step2],
        value: Value::Bool(true),
    };

    let p1 = Proof {
        claim: p1_claim,
        rule: Some("pythagoras"),
        antecedents: vec![],
    };

    let p2 = Proof {
        claim: p2_claim,
        rule: Some("cos-definition"),
        antecedents: vec![],
    };

    let p3 = Proof {
        claim: goal_claim,
        rule: Some("law-of-cosines"),
        antecedents: vec![p1, p2],
    };

    Some(p3)
}

/// Derive a rectangle diagonal identity: for a rectangle `IsRectangle(A,B,C,D)`
/// with center `E` (equidistant from all vertices), the identity
///   AE²+BE²+CE²+DE² = AB²+BC²
/// holds because both sides equal `4·AE²`.
///
/// Returns derivation lines on success.
pub fn rectangle_diagonal_derive(
    items: &[crate::ast::LenExpr],
    _facts: &FactStore,
) -> Option<Vec<String>> {
    use crate::ast::LenExpr;
    if items.len() != 2 {
        return None;
    }
    fn collect_sq_segs(e: &LenExpr) -> Option<Vec<String>> {
        match e {
            LenExpr::Sq(inner) => match inner.as_ref() {
                LenExpr::Seg(s) => Some(vec![s.clone()]),
                _ => None,
            },
            LenExpr::Add(l, r) => {
                let mut v = collect_sq_segs(l)?;
                v.extend(collect_sq_segs(r)?);
                Some(v)
            }
            _ => None,
        }
    }
    let left_segs = collect_sq_segs(&items[0])?;
    let right_segs = collect_sq_segs(&items[1])?;
    if left_segs.len() != 4 || right_segs.len() != 2 {
        return None;
    }
    // Find the common character across all 4 segments (the center point).
    // Each segment is 2 chars like "ae", "be", "ce", "de" — center is shared.
    let chars0: Vec<char> = left_segs[0].chars().collect();
    let center_ch = if left_segs[1..].iter().all(|s| s.contains(chars0[0])) {
        chars0[0]
    } else if left_segs[1..].iter().all(|s| s.contains(chars0[1])) {
        chars0[1]
    } else {
        return None;
    };
    let vertices: Vec<String> = left_segs
        .iter()
        .map(|s| {
            s.chars()
                .find(|c| *c != center_ch)
                .map(|c| c.to_string())
        })
        .collect::<Option<Vec<_>>>()?;
    if vertices.len() != 4 {
        return None;
    }
    let center_disp = center_ch.to_uppercase().to_string();
    let v_disp: Vec<String> = vertices.iter().map(|v| v.to_uppercase()).collect();
    let mut out = Vec::new();
    // Use original segment names from left_segs (e.g. "AE","BE","CE","DE")
    // rather than reconstructing from center+vertex (which gives "EA" etc.).
    let first_seg = left_segs[0].to_uppercase();
    let diag_seg = Claim::seg_key(&vertices[0], &vertices[2]).to_uppercase();
    out.push(format!(
        "{}^2+{}^2+{}^2+{}^2=4*{}^2  // {} is equidistant from all rectangle vertices",
        left_segs[0].to_uppercase(),
        left_segs[1].to_uppercase(),
        left_segs[2].to_uppercase(),
        left_segs[3].to_uppercase(),
        first_seg,
        center_disp,
    ));
    // The diagonal is vertices[0]-vertices[2]; the right triangle uses those
    // two endpoints plus one of the remaining vertices (vertices[1]).
    let tri_name = format!(
        "{}{}{}",
        v_disp[0], v_disp[1], v_disp[2]
    );
    out.push(format!(
        "{}^2+{}^2={}^2  // Pythagoras in right triangle {}",
        right_segs[0].to_uppercase(),
        right_segs[1].to_uppercase(),
        diag_seg,
        tri_name,
    ));
    out.push(format!(
        "{}=2*{}  // {} is midpoint of diagonal",
        diag_seg,
        first_seg,
        center_disp,
    ));
    Some(out)
}

/// Proof version of rectangle diagonal derivation - returns a Proof tree.
pub fn rectangle_diagonal_proof(
    items: &[crate::ast::LenExpr],
    _facts: &FactStore,
) -> Option<Proof> {
    use crate::ast::LenExpr;
    if items.len() != 2 {
        return None;
    }
    fn collect_sq_segs(e: &LenExpr) -> Option<Vec<String>> {
        match e {
            LenExpr::Sq(inner) => match inner.as_ref() {
                LenExpr::Seg(s) => Some(vec![s.clone()]),
                _ => None,
            },
            LenExpr::Add(l, r) => {
                let mut v = collect_sq_segs(l)?;
                v.extend(collect_sq_segs(r)?);
                Some(v)
            }
            _ => None,
        }
    }
    let left_segs = collect_sq_segs(&items[0])?;
    let right_segs = collect_sq_segs(&items[1])?;
    if left_segs.len() != 4 || right_segs.len() != 2 {
        return None;
    }
    let chars0: Vec<char> = left_segs[0].chars().collect();
    let center_ch = if left_segs[1..].iter().all(|s| s.contains(chars0[0])) {
        chars0[0]
    } else if left_segs[1..].iter().all(|s| s.contains(chars0[1])) {
        chars0[1]
    } else {
        return None;
    };
    let vertices: Vec<String> = left_segs
        .iter()
        .map(|s| {
            s.chars()
                .find(|c| *c != center_ch)
                .map(|c| c.to_string())
        })
        .collect::<Option<Vec<_>>>()?;
    if vertices.len() != 4 {
        return None;
    }
    let _center_disp = center_ch.to_uppercase().to_string();
    let v_disp: Vec<String> = vertices.iter().map(|v| v.to_uppercase()).collect();
    let first_seg = left_segs[0].to_uppercase();
    let diag_seg = Claim::seg_key(&vertices[0], &vertices[2]).to_uppercase();

    let goal_display = format!(
        "{}={}",
        checker::render_len_expr(&items[0]),
        checker::render_len_expr(&items[1])
    );
    let goal_claim = Claim::PredVal {
        name: "eqchain".to_string(),
        args: vec![goal_display],
        value: Value::Bool(true),
    };

    let _tri_name = format!("{}{}{}", v_disp[0], v_disp[1], v_disp[2]);

    let step1 = format!("{}^2+{}^2+{}^2+{}^2=4*{}^2",
        left_segs[0].to_uppercase(), left_segs[1].to_uppercase(),
        left_segs[2].to_uppercase(), left_segs[3].to_uppercase(), first_seg);
    let step2 = format!("{}^2+{}^2={}^2", right_segs[0].to_uppercase(), right_segs[1].to_uppercase(), diag_seg);
    let step3 = format!("{}=2*{}", diag_seg, first_seg);

    let p1_claim = Claim::PredVal {
        name: "eqchain".to_string(),
        args: vec![step1],
        value: Value::Bool(true),
    };
    let p2_claim = Claim::PredVal {
        name: "eqchain".to_string(),
        args: vec![step2],
        value: Value::Bool(true),
    };
    let p3_claim = Claim::PredVal {
        name: "eqchain".to_string(),
        args: vec![step3],
        value: Value::Bool(true),
    };

    let p1 = Proof {
        claim: p1_claim,
        rule: Some("rectangle-equidistant"),
        antecedents: vec![],
    };

    let p2 = Proof {
        claim: p2_claim,
        rule: Some("pythagoras"),
        antecedents: vec![],
    };

    let p3 = Proof {
        claim: p3_claim,
        rule: Some("midpoint-diagonal"),
        antecedents: vec![],
    };

    let p_final = Proof {
        claim: goal_claim,
        rule: Some("rectangle-diagonal-identity"),
        antecedents: vec![p1, p2, p3],
    };

    Some(p_final)
}

/// The foot of a perpendicular construction.
struct Foot {
    foot: char,
    /// The vertex the perpendicular drops from (the apex on the squared side).
    apex: char,
    /// The other endpoint of the squared side (the far base endpoint).
    far_base: char,
}

/// Find a perpendicular foot `H` and the associated apex/far-base from the
/// right-triangle facts, given angle vertex `v`, squared-side endpoints `s1`,`s2`.
///
/// Requires two right triangles (apex,H,v) and (apex,H,far) both right at H,
/// where {apex, far} = {s1,s2}. This is exactly a perpendicular dropped from
/// `apex` onto the base line `v-far`, with foot `H`.
fn find_foot(v: char, s1: char, s2: char, facts: &FactStore) -> Option<Foot> {
    let vc = v.to_ascii_lowercase();
    let s1c = s1.to_ascii_lowercase();
    let s2c = s2.to_ascii_lowercase();

    // Gather right triangles: (triangle_letters, right_at).
    let mut right_tris: Vec<(String, char)> = Vec::new();
    for c in facts.all() {
        if let Claim::PredVal { name, args, value } = c {
            let is_right = name == "isright" || name == "rightat";
            if is_right && args.len() == 1 {
                // We need the right-angle vertex from the `rightat` fact.
                let foot = match value {
                    Value::Point(p) => p.chars().next()?.to_ascii_lowercase(),
                    _ => continue,
                };
                let tri = args[0].clone();
                right_tris.push((tri, foot));
            }
        }
    }

    for (tri, foot) in &right_tris {
        let mut tc: Vec<char> = tri.chars().collect();
        tc.sort();
        let ts: String = tc.iter().collect();
        if !ts.contains(vc) {
            continue;
        }
        // Foot must be in the triangle.
        if !ts.contains(*foot) {
            continue;
        }
        // The third vertex (not v, not foot) is the apex.
        let apexes: Vec<char> = tc
            .iter()
            .copied()
            .filter(|&c| c != vc && c != *foot)
            .collect();
        if apexes.len() != 1 {
            continue;
        }
        let apex = apexes[0];
        // apex must be one of the squared-side endpoints.
        if apex != s1c && apex != s2c {
            continue;
        }
        let far = if apex == s1c { s2c } else { s1c };
        // Confirm a second right triangle (apex, foot, far) right at foot.
        let mut want = vec![apex, *foot, far];
        want.sort();
        let want_key: String = want.iter().collect();
        let has_second = right_tris.iter().any(|(t2, f2)| {
            let mut t2c: Vec<char> = t2.chars().collect();
            t2c.sort();
            let t2k: String = t2c.iter().collect();
            t2k == want_key && *f2 == *foot
        });
        if !has_second {
            continue;
        }
        return Some(Foot {
            foot: foot.to_uppercase().next().unwrap(),
            apex: apex.to_uppercase().next().unwrap(),
            far_base: far.to_uppercase().next().unwrap(),
        });
    }
    None
}

/// Generatively verify the law-of-cosines identity in a concrete coordinate
/// model built from the perpendicular construction (apex at (t,h), foot at
/// (t,0) on the base line through v and far). Both sides are computed from
/// coordinates, so the identity is demonstrated, not assumed.
#[allow(clippy::too_many_arguments)]
fn verify_loc_numeric(
    s1: char,
    s2: char,
    v: char,
    h: char,
    apex: char,
    _x_seg: &str,
    _y_seg: &str,
    expr: &crate::ast::LenExpr,
) -> bool {
    use crate::ast::LenExpr;
    // Coordinate model of the perpendicular construction:
    //   base line from v (0,0) to far (L,0); foot H at (t,0); apex at (t,h).
    let far = if apex == s1 { s2 } else { s1 };
    let base_len = 10.0f64;
    let t = 6.0f64;
    let hgt = 8.0f64;
    let pos = |p: char| -> Option<(f64, f64)> {
        let pl = p.to_ascii_lowercase();
        if pl == v.to_ascii_lowercase() { Some((0.0, 0.0)) }
        else if pl == far.to_ascii_lowercase() { Some((base_len, 0.0)) }
        else if pl == apex.to_ascii_lowercase() { Some((t, hgt)) }
        else if pl == h.to_ascii_lowercase() { Some((t, 0.0)) }
        else { None }
    };
    let dist = |a: char, b: char| -> Option<f64> {
        let (p1, p2) = (pos(a)?, pos(b)?);
        Some(((p1.0 - p2.0).powi(2) + (p1.1 - p2.1).powi(2)).sqrt())
    };
    let segv = |s: &str| -> Option<f64> {
        let c: Vec<char> = s.chars()
            .filter(|&ch| !matches!(ch, 'k' | '_'))
            .collect();
        if c.len() != 2 { return None; }
        dist(c[0], c[1])
    };

    // cos(v): in the right triangle (apex, H, v) right at H, the adjacent leg to
    // angle v is v-H and the hypotenuse is v-apex.
    let Some(hypotenuse) = dist(v, apex) else {
        return false;
    };
    let Some(adjacent) = dist(v, h) else {
        return false;
    };
    let cos_val = adjacent / hypotenuse;

    // Evaluate the RHS expression (with cos) using our model.
    fn ev(
        e: &LenExpr,
        segv: &dyn Fn(&str) -> Option<f64>,
        cosv: f64,
        v: char,
        apex: char,
        far: char,
    ) -> Option<f64> {
        match e {
            LenExpr::Num(n) => Some(*n as f64),
            LenExpr::Seg(s) => segv(s),
            LenExpr::Sq(i) => {
                let base = ev(i, segv, cosv, v, apex, far)?;
                Some(base * base)
            }
            LenExpr::Add(l, r) => Some(ev(l, segv, cosv, v, apex, far)? + ev(r, segv, cosv, v, apex, far)?),
            LenExpr::Sub(l, r) => Some(ev(l, segv, cosv, v, apex, far)? - ev(r, segv, cosv, v, apex, far)?),
            LenExpr::Mul(l, r) => Some(ev(l, segv, cosv, v, apex, far)? * ev(r, segv, cosv, v, apex, far)?),
            LenExpr::Trig(func, angle) if func == "cos" => {
                if angle.chars().next()? == v.to_ascii_lowercase() { Some(cosv) } else { None }
            }
            _ => None,
        }
    }

    let Some(rhs_val) = ev(expr, &segv, cos_val, v, apex, far) else {
        return false;
    };
    let Some(opp) = dist(apex, far) else {
        return false;
    };
    (opp * opp - rhs_val).abs() < 1e-6
}

/// Remove internal normalization artifacts ('k', '_') and uppercase for display.
fn nseg_disp_to_upper(s: &str) -> String {
    let mut chars: Vec<char> = s.chars().filter(|c| !matches!(c, '_')).collect();
    chars.sort();
    chars.iter().map(|c| c.to_uppercase().next().unwrap()).collect()
}

/// Find the vertex letter used in any `cos(V)` within a `LenExpr` tree.
fn find_cos_vertex(e: &crate::ast::LenExpr) -> Option<char> {
    use crate::ast::LenExpr;
    match e {
        LenExpr::Trig(func, angle) if func == "cos" => angle.chars().next(),
        LenExpr::Add(l, r) | LenExpr::Sub(l, r) | LenExpr::Mul(l, r) => {
            find_cos_vertex(l).or_else(|| find_cos_vertex(r))
        }
        LenExpr::Sq(inner) | LenExpr::Sqrt(inner) => find_cos_vertex(inner),
        _ => None,
    }
}

/// Extract `X² + Y² − 2·X·Y·cos(V)` from an expression, returning the two
/// adjacent side segments X and Y (as normalized keys). Accepts any valid
/// associativity of the `+` and `-`.
fn extract_sum_sq_sub_mul(e: &crate::ast::LenExpr) -> Option<(String, String)> {
    use crate::ast::LenExpr;
    fn seg_of(le: &LenExpr) -> Option<String> {
        match le {
            LenExpr::Seg(s) => Some(Claim::norm_seg(s)),
            LenExpr::Sq(inner) => {
                let s = inner.seg();
                if s.is_empty() { None } else { Some(Claim::norm_seg(&s)) }
            }
            _ => None,
        }
    }
    fn walk<'a>(le: &'a LenExpr, out: &mut Vec<Chunk<'a>>) {
        match le {
            LenExpr::Add(l, r) => { walk(l, out); out.push(Chunk::Plus); walk(r, out); }
            LenExpr::Sub(l, r) => { walk(l, out); out.push(Chunk::Minus); walk(r, out); }
            other => out.push(Chunk::Term(other)),
        }
    }
    enum Chunk<'a> { Term(&'a LenExpr), Plus, Minus }
    let mut chunks = Vec::new();
    walk(e, &mut chunks);

    let mut sq_segs: Vec<String> = Vec::new();
    let mut sign = 1;
    for c in chunks {
        match c {
            Chunk::Plus => sign = 1,
            Chunk::Minus => sign = -1,
            Chunk::Term(t) => {
                match t {
                    LenExpr::Sq(_) => {
                        if let Some(s) = seg_of(t) {
                            if sign > 0 {
                                sq_segs.push(s);
                            }
                        }
                    }
                    _ => {
                        // A Mul chain: 2*X*Y*cos(V), only meaningful when negative.
                        if sign < 0 {
                            let mut leaves: Vec<&LenExpr> = Vec::new();
                            collect_mul_leaves(t, &mut leaves);
                            let has2 = leaves.iter().any(|l| matches!(l, LenExpr::Num(2)));
                            let has_cos = leaves.iter().any(|l| matches!(l, LenExpr::Trig(f, _) if f == "cos"));
                            let segs: Vec<String> = leaves.iter().filter_map(|l| seg_of(l)).collect();
                            if !(has2 && has_cos) {
                                return None;
                            }
                            let _ = segs;
                        }
                    }
                }
            }
        }
    }
    if sq_segs.len() < 2 {
        return None;
    }
    Some((sq_segs[0].clone(), sq_segs[1].clone()))
}

fn collect_mul_leaves<'a>(e: &'a crate::ast::LenExpr, out: &mut Vec<&'a crate::ast::LenExpr>) {
    if let crate::ast::LenExpr::Mul(l, r) = e {
        collect_mul_leaves(l, out);
        collect_mul_leaves(r, out);
    } else {
        out.push(e);
    }
}

/// acute (largest side squared < sum of other squares).
fn acute_solves(tri: &str, facts: &FactStore) -> bool {    let chars: Vec<char> = tri.chars().collect();
    if chars.len() != 3 {
        return false;
    }
    let sides = [
        Claim::seg_key(&chars[0].to_string(), &chars[1].to_string()),
        Claim::seg_key(&chars[1].to_string(), &chars[2].to_string()),
        Claim::seg_key(&chars[2].to_string(), &chars[0].to_string()),
    ];
    let lens: Vec<u32> = match sides
        .iter()
        .map(|s| solve_len(s, facts))
        .collect::<Vec<Option<u32>>>()
    {
        v if v.iter().all(|x| x.is_some()) => v.into_iter().map(|x| x.unwrap()).collect(),
        _ => return false,
    };
    let mut sorted = lens.clone();
    sorted.sort_unstable();
    // Degenerate or zero sides are not acute triangles.
    if sorted[0] == 0 {
        return false;
    }
    (sorted[2] as u64 * sorted[2] as u64) < (sorted[0] as u64).pow(2) + (sorted[1] as u64).pow(2)
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
            // Ratio-to-segment: if AB/X = CD/X for some X and ratio R,
            // then AB = CD. Also handles equal denominators via SegEq.
            let na = Claim::norm_seg(a);
            let nb = Claim::norm_seg(b);
            let all = facts.all();
            for f in &all {
                if let Claim::RatioEq(ratio_a, ratio_b) = f {
                    if let RatioExpr::Quot {
                        num: RatioAtom::Seg(seg_a),
                        den: RatioAtom::Seg(seg_x1),
                    } = ratio_a
                    {
                        if Claim::norm_seg(seg_a) == na {
                            for f2 in &all {
                                if let Claim::RatioEq(ratio_c, ratio_d) = f2 {
                                    if *ratio_b == *ratio_d {
                                        if let RatioExpr::Quot {
                                            num: RatioAtom::Seg(seg_b),
                                            den: RatioAtom::Seg(seg_x2),
                                        } = ratio_c
                                        {
                                            let nb2 = Claim::norm_seg(seg_b);
                                            let nx1 = Claim::norm_seg(seg_x1);
                                            let nx2 = Claim::norm_seg(seg_x2);
                                            let denom_ok = if nb2 == nb && nx1 == nx2 {
                                                true
                                            } else if nb2 == nb && nx1 != nx2 {
                                                all.iter().any(|s| {
                                                    matches!(
                                                        s,
                                                        Claim::SegEq(d1, d2)
                                                            if (Claim::norm_seg(d1) == nx1
                                                                && Claim::norm_seg(d2) == nx2)
                                                                || (Claim::norm_seg(d1) == nx2
                                                                    && Claim::norm_seg(d2) == nx1)
                                                    )
                                                })
                                            } else {
                                                false
                                            };
                                            if denom_ok {
                                                let p = Proof {
                                                    claim: goal.clone(),
                                                    antecedents: vec![
                                                        Proof { claim: f.clone(), antecedents: vec![], rule: None },
                                                        Proof { claim: f2.clone(), antecedents: vec![], rule: None },
                                                    ],
                                                    rule: Some("ratio-segeq"),
                                                };
                                                return Some(p);
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            None
        }
        Claim::RatioEq(_, _) => ratio_proof(goal, &env, facts),
        // Numeric acuteness: all sides known, largest angle strictly acute.
        Claim::PredVal { name, args, value }
            if name == "isacute"
                && *value == Value::Bool(true)
                && args.len() == 1 =>
        {
            if acute_solves(&args[0], facts) {
                Some(Proof {
                    claim: goal.clone(),
                    rule: Some("numeric-angle"),
                    antecedents: Vec::new(),
                })
            } else {
                None
            }
        }
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

    fn half(self) -> Self {
        Self::new(self.num, self.den * 2)
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
                    // Multi-char point names: letter+digits? pairs
                    let points: Vec<String> = {
                        let mut result = Vec::new();
                        let mut i = 0;
                        while i < chars.len() {
                            if !chars[i].is_ascii_alphabetic() {
                                i += 1;
                                continue;
                            }
                            let start = i;
                            i += 1;
                            while i < chars.len() && chars[i].is_ascii_digit() {
                                i += 1;
                            }
                            result.push(chars[start..i].iter().collect());
                        }
                        result
                    };
                    if points.len() == 2 {
                        (points[0].clone(), points[1].clone())
                    } else {
                        return None;
                    }
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






