//! Geometry rule base and pattern-matching engine.
//!
//! Rules map premises to conclusions. Each `->` in a proof chain is a single
//! rule application, so a proof is a sequence of rule applications. The rule
//! patterns use variables (upper-case letters) that unify with concrete
//! references from the fact store.

use crate::claim::{Claim, RatioAtom, RatioExpr, Value};
use std::collections::HashMap;

/// A pattern expression: matches part of a reference.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[allow(dead_code)]
pub enum PExpr {
    /// A single point variable, matches a one-character ref.
    PtVar(String),
    /// A two-point segment `(a, b)` (order-insensitive).
    Seg2(String, String),
    /// A three-point triangle `(a, b, c)`.
    Tri3(String, String, String),
    /// A literal point ref.
    PtRef(String),
    /// A literal segment ref (orientation-insensitive).
    SegRef(String),
    /// A literal triangle ref.
    TriRef(String),
    /// A variable holding a whole ref (e.g. a triangle name).
    AnyRef(String),
}

/// An atom inside a ratio pattern: a segment expression or an integer literal.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PRatioAtom {
    Expr(PExpr),
    Int(u32),
}

/// A ratio expression pattern: a bare segment, a quotient, or an integer
/// literal.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PRatioExpr {
    Seg(PExpr),
    Quot { num: PRatioAtom, den: PRatioAtom },
    Int(u32),
}

/// A claim pattern.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PClaim {
    SegEq(PExpr, PExpr),
    /// Equality of two triangles, e.g. `ABC = MNP`.
    TriEq(PExpr, PExpr),
    /// Equality of two angles, e.g. `Angle(ABC) = Angle(MNP)`.
    AngleEq(PExpr, PExpr),
    /// Equality of two ratios, e.g. `BD/DC = AB/AC`.
    RatioEq(PRatioExpr, PRatioExpr),
    PredVal(String, Vec<PExpr>, Value),
    /// A predicate whose value is a point pattern, e.g. `rightAt(T) = X`.
    PredAt(String, Vec<PExpr>, PExpr),
    On(PExpr, PExpr),
    IsoscelesAt(PExpr, PExpr),
    OnSameCircle(Vec<PExpr>),
}

/// A single derivation rule.
#[derive(Debug, Clone)]
pub struct Rule {
    pub id: &'static str,
    /// Premises that must be established (part of the proof chain).
    pub antecedents: Vec<PClaim>,
    /// Side conditions that must already be facts (not shown in the chain).
    pub requires: Vec<PClaim>,
    pub consequent: PClaim,
}

pub type Bindings = HashMap<String, String>;

fn try_bind(var: &str, val: &str, bind: &Bindings) -> Vec<Bindings> {
    if let Some(existing) = bind.get(var) {
        if existing == val {
            vec![bind.clone()]
        } else {
            vec![]
        }
    } else {
        let mut b = bind.clone();
        b.insert(var.to_string(), val.to_string());
        vec![b]
    }
}

/// Match a reference against a pattern expression, enumerating bindings.
pub fn match_expr(refval: &str, e: &PExpr, bind: &Bindings) -> Vec<Bindings> {
    match e {
        PExpr::PtVar(v) => {
            // Match any point name (single or multi-char).
            // The reference value is already normalized (lowercase).
            try_bind(v, refval, bind)
        }
        PExpr::Seg2(v1, v2) => {
            // Handle both legacy 2-char segments ("ab") and multi-char with delimiter ("p1-p2")
            let (a, b) = if refval.contains('-') {
                let parts: Vec<&str> = refval.split('-').collect();
                if parts.len() == 2 {
                    (parts[0].to_string(), parts[1].to_string())
                } else {
                    return vec![];
                }
            } else if refval.len() == 2 {
                (refval[0..1].to_string(), refval[1..2].to_string())
            } else {
                return vec![];
            };
            let mut out = Vec::new();
            if let Some(fb) = try_bind(v1, &a, bind).into_iter().next() {
                out.extend(try_bind(v2, &b, &fb));
            }
            if let Some(fb) = try_bind(v1, &b, bind).into_iter().next() {
                out.extend(try_bind(v2, &a, &fb));
            }
            out
        }
        PExpr::Tri3(v1, v2, v3) => {
            if refval.len() == 3 {
                let a = refval[0..1].to_string();
                let b = refval[1..2].to_string();
                let c = refval[2..3].to_string();
                // Angles normalize their two arms (first and third char), so
                // try both arm orders as well as the positional order.
                let mut out: Vec<Bindings> = try_bind(v1, &a, bind);
                out = out
                    .iter()
                    .flat_map(|b0| try_bind(v2, &b, b0))
                    .collect();
                out = out
                    .iter()
                    .flat_map(|b0| try_bind(v3, &c, b0))
                    .collect();
                let mut swapped: Vec<Bindings> = try_bind(v1, &c, bind);
                swapped = swapped
                    .iter()
                    .flat_map(|b0| try_bind(v2, &b, b0))
                    .collect();
                swapped = swapped
                    .iter()
                    .flat_map(|b0| try_bind(v3, &a, b0))
                    .collect();
                out.extend(swapped);
                out
            } else {
                vec![]
            }
        }
        PExpr::PtRef(p) => {
            if refval == p {
                vec![bind.clone()]
            } else {
                vec![]
            }
        }
        PExpr::SegRef(s) => {
            if Claim::norm_seg(refval) == Claim::norm_seg(s) {
                vec![bind.clone()]
            } else {
                vec![]
            }
        }
        PExpr::TriRef(t) => {
            if refval == t {
                vec![bind.clone()]
            } else {
                vec![]
            }
        }
        PExpr::AnyRef(v) => try_bind(v, refval, bind),
    }
}

/// Match a claim against a claim pattern, enumerating bindings.
pub fn match_pat(claim: &Claim, pat: &PClaim, bind: &Bindings) -> Vec<Bindings> {
    match (claim, pat) {
        (Claim::SegEq(a, b), PClaim::SegEq(pa, pb)) => {
            let mut out = Vec::new();
            // Claims are pair-canonical and patterns may be written in either
            // order, so try all four pairings.
            for b1 in match_expr(a, pa, bind) {
                out.extend(match_expr(b, pb, &b1));
            }
            for b1 in match_expr(a, pb, bind) {
                out.extend(match_expr(b, pa, &b1));
            }
            out
        }
        (
            Claim::PredVal { name, args, value },
            PClaim::PredVal(pn, pargs, pv),
        ) if name == pn && value == pv && args.len() == pargs.len() => {
            let mut out = Vec::new();
            let mut cur = vec![bind.clone()];
            for (arg, pe) in args.iter().zip(pargs.iter()) {
                let mut next = Vec::new();
                for b in &cur {
                    next.extend(match_expr(arg, pe, b));
                }
                cur = next;
            }
            out.extend(cur);
            // Symmetric two-segment predicates also match with the fact's
            // arguments swapped (IsPerpendicular(AI,EF) == (EF,AI)).
            let symmetric = args.len() == 2
                && matches!(
                    name.as_str(),
                    "isparallel" | "isperpendicular" | "isequal" | "equals"
                );
            if symmetric {
                let mut cur = vec![bind.clone()];
                for (arg, pe) in args.iter().rev().zip(pargs.iter()) {
                    let mut next = Vec::new();
                    for b in &cur {
                        next.extend(match_expr(arg, pe, b));
                    }
                    cur = next;
                }
                out.extend(cur);
            }
            out
        }
        (
            Claim::PredVal { name, args, value },
            PClaim::PredAt(pn, pargs, pe),
        ) if name == pn && args.len() == pargs.len() => {
            let mut cur = vec![bind.clone()];
            for (arg, pexpr) in args.iter().zip(pargs.iter()) {
                let mut next = Vec::new();
                for b in &cur {
                    next.extend(match_expr(arg, pexpr, b));
                }
                cur = next;
            }
            let pt = match value {
                Value::Point(p) => p.clone(),
                _ => return vec![],
            };
            let mut out = Vec::new();
            for b in cur {
                out.extend(match_expr(&pt, pe, &b));
            }
            out
        }
        (Claim::TriEq(a, b), PClaim::TriEq(pa, pb)) => {
            let mut out = Vec::new();
            for b1 in match_expr(a, pa, bind) {
                out.extend(match_expr(b, pb, &b1));
            }
            out
        }
        (Claim::AngleEq(a, b), PClaim::AngleEq(pa, pb)) => {
            let mut out = Vec::new();
            for b1 in match_expr(a, pa, bind) {
                out.extend(match_expr(b, pb, &b1));
            }
            out
        }
        (Claim::RatioEq(l, r), PClaim::RatioEq(pl, pr)) => {
            // Try both side orderings (claims are stored with the sides sorted).
            let mut out = Vec::new();
            for b1 in match_ratio(l, pl, bind) {
                out.extend(match_ratio(r, pr, &b1));
            }
            for b1 in match_ratio(l, pr, bind) {
                out.extend(match_ratio(r, pl, &b1));
            }
            out
        }
        (Claim::On(p, s), PClaim::On(pp, ps)) => {
            let mut out = Vec::new();
            for b1 in match_expr(p, pp, bind) {
                out.extend(match_expr(s, ps, &b1));
            }
            out
        }
        (Claim::IsoscelesAt(t, a), PClaim::IsoscelesAt(pt, pa)) => {
            let mut out = Vec::new();
            for b1 in match_expr(t, pt, bind) {
                out.extend(match_expr(a, pa, &b1));
            }
            out
        }
        (Claim::OnSameCircle(pts), PClaim::OnSameCircle(pps)) => {
            if pts.len() != pps.len() {
                return vec![];
            }
            let mut cur = vec![bind.clone()];
            for (pt, pp) in pts.iter().zip(pps.iter()) {
                let mut next = Vec::new();
                for b in &cur {
                    next.extend(match_expr(pt, pp, b));
                }
                cur = next;
                if cur.is_empty() {
                    return vec![];
                }
            }
            cur
        }
        _ => vec![],
    }
}

/// Match a ratio atom against a ratio-atom pattern.
fn match_atom(claim: &RatioAtom, pat: &PRatioAtom, bind: &Bindings) -> Vec<Bindings> {
    match (claim, pat) {
        (RatioAtom::Seg(c), PRatioAtom::Expr(p)) => match_expr(c, p, bind),
        (RatioAtom::Int(n), PRatioAtom::Int(m)) if n == m => vec![bind.clone()],
        _ => vec![],
    }
}

/// Match a ratio expression against a ratio pattern. Quotients may match in
/// either orientation (claims are stored with the smaller atom as numerator).
fn match_ratio(claim: &RatioExpr, pat: &PRatioExpr, bind: &Bindings) -> Vec<Bindings> {
    match (claim, pat) {
        (RatioExpr::Seg(c), PRatioExpr::Seg(p)) => match_expr(c, p, bind),
        (
            RatioExpr::Quot { num, den },
            PRatioExpr::Quot { num: pn, den: pd },
        ) => {
            let mut out = Vec::new();
            for b1 in match_atom(num, pn, bind) {
                out.extend(match_atom(den, pd, &b1));
            }
            for b1 in match_atom(num, pd, bind) {
                out.extend(match_atom(den, pn, &b1));
            }
            out
        }
        _ => vec![],
    }
}

/// Render a pattern expression into a reference string using the bindings.
pub fn render_expr(e: &PExpr, bind: &Bindings) -> String {
    match e {
        PExpr::PtVar(v) | PExpr::AnyRef(v) => bind.get(v).cloned().unwrap_or_default(),
        PExpr::Seg2(a, b) => {
            let x = bind.get(a).cloned().unwrap_or_default();
            let y = bind.get(b).cloned().unwrap_or_default();
            // Use - delimiter for multi-char points
            if x.len() > 1 || y.len() > 1 {
                format!("{}-{}", x, y)
            } else {
                format!("{}{}", x, y)
            }
        }
        PExpr::Tri3(a, b, c) => {
            let x = bind.get(a).cloned().unwrap_or_default();
            let y = bind.get(b).cloned().unwrap_or_default();
            let z = bind.get(c).cloned().unwrap_or_default();
            format!("{}{}{}", x, y, z)
        }
        PExpr::PtRef(p) => p.clone(),
        PExpr::SegRef(s) => s.clone(),
        PExpr::TriRef(t) => t.clone(),
    }
}

/// Render a ratio-atom pattern into a concrete ratio atom.
fn render_patom(p: &PRatioAtom, bind: &Bindings) -> RatioAtom {
    match p {
        PRatioAtom::Expr(e) => RatioAtom::Seg(render_expr(e, bind)),
        PRatioAtom::Int(n) => RatioAtom::Int(*n),
    }
}

/// Render a ratio-expression pattern into a concrete ratio expression.
fn render_pratio(p: &PRatioExpr, bind: &Bindings) -> RatioExpr {
    match p {
        PRatioExpr::Seg(e) => RatioExpr::Seg(render_expr(e, bind)),
        PRatioExpr::Quot { num, den } => RatioExpr::Quot {
            num: render_patom(num, bind),
            den: render_patom(den, bind),
        },
        PRatioExpr::Int(n) => RatioExpr::Seg(n.to_string()),
    }
}

/// Instantiate a claim pattern with bindings into a concrete claim.
pub fn instantiate(pat: &PClaim, bind: &Bindings) -> Claim {
    match pat {
        PClaim::SegEq(a, b) => {
            let s1 = render_expr(a, bind);
            let s2 = render_expr(b, bind);
            Claim::seg_eq(&s1, &s2)
        }
        PClaim::TriEq(a, b) => {
            let s1 = render_expr(a, bind);
            let s2 = render_expr(b, bind);
            Claim::tri_eq(&s1, &s2)
        }
        PClaim::AngleEq(a, b) => {
            let s1 = render_expr(a, bind);
            let s2 = render_expr(b, bind);
            Claim::angle_eq(&s1, &s2)
        }
        PClaim::RatioEq(l, r) => {
            let lhs = render_pratio(l, bind);
            let rhs = render_pratio(r, bind);
            Claim::ratio_eq(&lhs, &rhs)
        }
        PClaim::PredVal(name, args, value) => {
            let args: Vec<String> = args.iter().map(|a| render_expr(a, bind)).collect();
            Claim::PredVal { name: name.clone(), args, value: value.clone() }
        }
        PClaim::PredAt(name, args, pe) => {
            let args: Vec<String> = args.iter().map(|a| render_expr(a, bind)).collect();
            let p = render_expr(pe, bind);
            Claim::PredVal { name: name.clone(), args, value: Value::Point(p) }
        }
        PClaim::On(p, s) => {
            Claim::On(render_expr(p, bind), Claim::norm_seg(&render_expr(s, bind)))
        }
        PClaim::IsoscelesAt(t, a) => {
            Claim::IsoscelesAt(render_expr(t, bind), render_expr(a, bind))
        }
        PClaim::OnSameCircle(pts) => {
            let pts: Vec<String> = pts.iter().map(|p| render_expr(p, bind)).collect();
            Claim::OnSameCircle(pts)
        }
    }
}

/// Enumerate all ways to apply `rule` so that its consequent equals `goal`,
/// its antecedents are established in `facts` or given in `extra`, and its
/// side conditions hold in `facts`.
pub fn apply_rule(
    rule: &Rule,
    facts: &[Claim],
    extra: &[Claim],
    goal: &Claim,
) -> Vec<Bindings> {
    let candidates: Vec<&Claim> = facts.iter().chain(extra.iter()).collect();
    let mut results = Vec::new();

    for b0 in match_pat(goal, &rule.consequent, &HashMap::new()) {
        let mut cur = vec![b0];
        for ant in &rule.antecedents {
            let mut next = Vec::new();
            for bind in &cur {
                for cand in &candidates {
                    next.extend(match_pat(cand, ant, bind));
                }
            }
            cur = next;
            if cur.is_empty() {
                break;
            }
        }
        for bind in cur {
            let mut ok = true;
            for req in &rule.requires {
                if !facts.contains(&instantiate(req, &bind)) {
                    ok = false;
                    break;
                }
            }
            if ok {
                results.push(bind);
            }
        }
    }
    results
}

fn same_shape(a: &Claim, b: &Claim) -> bool {
    match (a, b) {
        (Claim::SegEq(..), Claim::SegEq(..)) => true,
        (Claim::TriEq(..), Claim::TriEq(..)) => true,
        (Claim::RatioEq(..), Claim::RatioEq(..)) => true,
        (
            Claim::PredVal { name: n1, args: a1, .. },
            Claim::PredVal { name: n2, args: a2, .. },
        ) => n1 == n2 && a1.len() == a2.len(),
        _ => false,
    }
}

/// Find a "closest" expected result for a goal that no rule derives: look for
/// rules whose premises are already established, and suggest the consequent
/// they would have produced (used to build `hint:` messages).
pub fn find_hint(
    facts: &[Claim],
    extra: &[Claim],
    goal: &Claim,
    rules: &[Rule],
) -> Option<Claim> {
    let candidates: Vec<&Claim> = facts.iter().chain(extra.iter()).collect();
    for rule in rules {
        let mut cur = vec![Bindings::new()];
        for ant in &rule.antecedents {
            let mut next = Vec::new();
            for bind in &cur {
                for cand in &candidates {
                    next.extend(match_pat(cand, ant, bind));
                }
            }
            cur = next;
            if cur.is_empty() {
                break;
            }
        }
        for bind in cur {
            let mut ok = true;
            for req in &rule.requires {
                if !facts.contains(&instantiate(req, &bind)) {
                    ok = false;
                    break;
                }
            }
            if !ok {
                continue;
            }
            let cons = instantiate(&rule.consequent, &bind);
            if same_shape(&cons, goal) && cons != *goal {
                return Some(cons);
            }
        }
    }
    None
}

/// The built-in geometry rule set.
///
/// * `isosceles-altitude`: in an isosceles triangle with apex `P` and base
///   `QR`, the altitude from `P` to `QR` meets the base at its midpoint, so
///   the foot `W` is the median point of `QR`.
/// * `median-midpoint`: if `W` is the median point of segment `YZ` then the
///   two halves are equal: `WY = WZ`.
pub fn rule_base() -> Vec<Rule> {
    vec![
        Rule {
            id: "isosceles-altitude",
            antecedents: vec![
                PClaim::PredVal(
                    "isisosceles".into(),
                    vec![PExpr::AnyRef("T".into())],
                    Value::Bool(true),
                ),
                PClaim::PredVal(
                    "isperpendicular".into(),
                    vec![
                        PExpr::Seg2("P".into(), "W".into()),
                        PExpr::Seg2("Q".into(), "R".into()),
                    ],
                    Value::Bool(true),
                ),
            ],
            requires: vec![
                PClaim::IsoscelesAt(PExpr::AnyRef("T".into()), PExpr::PtVar("P".into())),
                PClaim::On(PExpr::PtVar("W".into()), PExpr::Seg2("Q".into(), "R".into())),
            ],
            consequent: PClaim::PredVal(
                "ismedian".into(),
                vec![PExpr::PtVar("W".into()), PExpr::Seg2("Q".into(), "R".into())],
                Value::Bool(true),
            ),
        },
        Rule {
            id: "median-midpoint",
            antecedents: vec![PClaim::PredVal(
                "ismedian".into(),
                vec![
                    PExpr::PtVar("W".into()),
                    PExpr::Seg2("Y".into(), "Z".into()),
                ],
                Value::Bool(true),
            )],
            requires: vec![],
            consequent: PClaim::SegEq(
                PExpr::Seg2("W".into(), "Y".into()),
                PExpr::Seg2("W".into(), "Z".into()),
            ),
        },
        // If `Z` lies on the line `XY`, `Y` is one of its defining points,
        // and `ZY = XY`, then `Y` is the midpoint of `XZ` (the point `Z` is
        // the reflection of `X` across `Y`).
        Rule {
            id: "reflection-midpoint",
            antecedents: vec![
                PClaim::On(
                    PExpr::PtVar("X".into()),
                    PExpr::Seg2("X".into(), "Y".into()),
                ),
                PClaim::On(
                    PExpr::PtVar("Y".into()),
                    PExpr::Seg2("X".into(), "Y".into()),
                ),
                PClaim::On(
                    PExpr::PtVar("Z".into()),
                    PExpr::Seg2("X".into(), "Y".into()),
                ),
                PClaim::SegEq(
                    PExpr::Seg2("Z".into(), "Y".into()),
                    PExpr::Seg2("X".into(), "Y".into()),
                ),
            ],
            requires: vec![],
            consequent: PClaim::PredVal(
                "ismedian".into(),
                vec![
                    PExpr::PtVar("Y".into()),
                    PExpr::Seg2("X".into(), "Z".into()),
                ],
                Value::Bool(true),
            ),
        },
        // In a right triangle the midpoint of the hypotenuse is the
        // circumcenter: the midpoint `W` of `YZ` is equidistant from the
        // right-angle vertex `X` and from both ends of the hypotenuse.
        Rule {
            id: "right-triangle-circumcenter-y",
            antecedents: vec![
                PClaim::PredVal(
                    "ismedian".into(),
                    vec![
                        PExpr::PtVar("W".into()),
                        PExpr::Seg2("Y".into(), "Z".into()),
                    ],
                    Value::Bool(true),
                ),
                PClaim::PredVal(
                    "isright".into(),
                    vec![PExpr::AnyRef("T".into())],
                    Value::Bool(true),
                ),
            ],
            requires: vec![PClaim::PredAt(
                "rightat".into(),
                vec![PExpr::AnyRef("T".into())],
                PExpr::PtVar("X".into()),
            )],
            consequent: PClaim::SegEq(
                PExpr::Seg2("W".into(), "Y".into()),
                PExpr::Seg2("W".into(), "X".into()),
            ),
        },
        Rule {
            id: "right-triangle-circumcenter-z",
            antecedents: vec![
                PClaim::PredVal(
                    "ismedian".into(),
                    vec![
                        PExpr::PtVar("W".into()),
                        PExpr::Seg2("Y".into(), "Z".into()),
                    ],
                    Value::Bool(true),
                ),
                PClaim::PredVal(
                    "isright".into(),
                    vec![PExpr::AnyRef("T".into())],
                    Value::Bool(true),
                ),
            ],
            requires: vec![PClaim::PredAt(
                "rightat".into(),
                vec![PExpr::AnyRef("T".into())],
                PExpr::PtVar("X".into()),
            )],
            consequent: PClaim::SegEq(
                PExpr::Seg2("W".into(), "Z".into()),
                PExpr::Seg2("W".into(), "X".into()),
            ),
        },
        // SAS triangle equality: if two sides and the angle included between
        // them are equal, the triangles are equal.
        Rule {
            id: "sas-triangle-equality",
            antecedents: vec![
                PClaim::SegEq(
                    PExpr::Seg2("A".into(), "B".into()),
                    PExpr::Seg2("M".into(), "N".into()),
                ),
                PClaim::SegEq(
                    PExpr::Seg2("B".into(), "C".into()),
                    PExpr::Seg2("N".into(), "P".into()),
                ),
                PClaim::AngleEq(
                    PExpr::Tri3("A".into(), "B".into(), "C".into()),
                    PExpr::Tri3("M".into(), "N".into(), "P".into()),
                ),
            ],
            requires: vec![],
            consequent: PClaim::TriEq(
                PExpr::Tri3("A".into(), "B".into(), "C".into()),
                PExpr::Tri3("M".into(), "N".into(), "P".into()),
            ),
        },
        // SSS triangle equality: if the three corresponding sides of two
        // triangles are pairwise equal, the triangles are equal. The vertex
        // correspondence is fixed by the three side pairs; triangle equality
        // itself is invariant under permutations of either side.
                Rule {
            id: "sss-triangle-equality",
            antecedents: vec![
                PClaim::SegEq(
                    PExpr::Seg2("A".into(), "B".into()),
                    PExpr::Seg2("M".into(), "N".into()),
                ),
                PClaim::SegEq(
                    PExpr::Seg2("B".into(), "C".into()),
                    PExpr::Seg2("N".into(), "P".into()),
                ),
                PClaim::SegEq(
                    PExpr::Seg2("A".into(), "C".into()),
                    PExpr::Seg2("M".into(), "P".into()),
                ),
            ],
            requires: vec![],
            consequent: PClaim::TriEq(
                PExpr::Tri3("A".into(), "B".into(), "C".into()),
                PExpr::Tri3("M".into(), "N".into(), "P".into()),
            ),
        },
        // AA similarity: two pairs of equal angles imply the triangles are
        // similar (the third pair follows automatically).
        Rule {
            id: "aa-similarity",
            antecedents: vec![
                PClaim::AngleEq(
                    PExpr::Tri3("A".into(), "B".into(), "C".into()),
                    PExpr::Tri3("M".into(), "N".into(), "P".into()),
                ),
                PClaim::AngleEq(
                    PExpr::Tri3("A".into(), "C".into(), "B".into()),
                    PExpr::Tri3("M".into(), "P".into(), "N".into()),
                ),
            ],
            requires: vec![],
            consequent: PClaim::PredVal(
                "issimilar".into(),
                vec![
                    PExpr::Tri3("A".into(), "B".into(), "C".into()),
                    PExpr::Tri3("M".into(), "N".into(), "P".into()),
                ],
                Value::Bool(true),
            ),
        },
        // SAS similarity: two proportional sides (equal here) and the angle
        // included between them imply similarity.
        Rule {
            id: "sas-similarity",
            antecedents: vec![
                PClaim::SegEq(
                    PExpr::Seg2("A".into(), "B".into()),
                    PExpr::Seg2("M".into(), "N".into()),
                ),
                PClaim::SegEq(
                    PExpr::Seg2("A".into(), "C".into()),
                    PExpr::Seg2("M".into(), "P".into()),
                ),
                PClaim::AngleEq(
                    PExpr::Tri3("B".into(), "A".into(), "C".into()),
                    PExpr::Tri3("N".into(), "M".into(), "P".into()),
                ),
            ],
            requires: vec![],
            consequent: PClaim::PredVal(
                "issimilar".into(),
                vec![
                    PExpr::Tri3("A".into(), "B".into(), "C".into()),
                    PExpr::Tri3("M".into(), "N".into(), "P".into()),
                ],
                Value::Bool(true),
            ),
        },
        // SSS similarity: three corresponding sides equal imply similarity.
        Rule {
            id: "sss-similarity",
            antecedents: vec![
                PClaim::SegEq(
                    PExpr::Seg2("A".into(), "B".into()),
                    PExpr::Seg2("M".into(), "N".into()),
                ),
                PClaim::SegEq(
                    PExpr::Seg2("B".into(), "C".into()),
                    PExpr::Seg2("N".into(), "P".into()),
                ),
                PClaim::SegEq(
                    PExpr::Seg2("A".into(), "C".into()),
                    PExpr::Seg2("M".into(), "P".into()),
                ),
            ],
            requires: vec![],
            consequent: PClaim::PredVal(
                "issimilar".into(),
                vec![
                    PExpr::Tri3("A".into(), "B".into(), "C".into()),
                    PExpr::Tri3("M".into(), "N".into(), "P".into()),
                ],
                Value::Bool(true),
            ),
        },
        // Equal (congruent) triangles are similar.
        Rule {
            id: "equal-implies-similar",
            antecedents: vec![PClaim::TriEq(
                PExpr::Tri3("A".into(), "B".into(), "C".into()),
                PExpr::Tri3("M".into(), "N".into(), "P".into()),
            )],
            requires: vec![],
            consequent: PClaim::PredVal(
                "issimilar".into(),
                vec![
                    PExpr::Tri3("A".into(), "B".into(), "C".into()),
                    PExpr::Tri3("M".into(), "N".into(), "P".into()),
                ],
                Value::Bool(true),
            ),
        },
        // An angle bisector splits its angle into two equal angles.
        Rule {
            id: "angle-bisector-equal-angles",
            antecedents: vec![
                PClaim::PredVal(
                    "isanglebisector".into(),
                    vec![
                        PExpr::Seg2("A".into(), "D".into()),
                        PExpr::Tri3("B".into(), "A".into(), "C".into()),
                    ],
                    Value::Bool(true),
                ),
                PClaim::On(PExpr::PtVar("D".into()), PExpr::Seg2("B".into(), "C".into())),
            ],
            requires: vec![],
            consequent: PClaim::AngleEq(
                PExpr::Tri3("B".into(), "A".into(), "D".into()),
                PExpr::Tri3("D".into(), "A".into(), "C".into()),
            ),
        },
        // In an isosceles triangle the apex angle bisector is also the median.
        Rule {
            id: "isosceles-apex-bisector-median",
            antecedents: vec![
                PClaim::PredVal(
                    "isisosceles".into(),
                    vec![PExpr::AnyRef("T".into())],
                    Value::Bool(true),
                ),
                PClaim::PredVal(
                    "isanglebisector".into(),
                    vec![
                        PExpr::Seg2("A".into(), "P".into()),
                        PExpr::Tri3("B".into(), "A".into(), "C".into()),
                    ],
                    Value::Bool(true),
                ),
            ],
            requires: vec![
                PClaim::IsoscelesAt(PExpr::AnyRef("T".into()), PExpr::PtVar("A".into())),
                PClaim::On(PExpr::PtVar("P".into()), PExpr::Seg2("B".into(), "C".into())),
            ],
            consequent: PClaim::PredVal(
                "ismedian".into(),
                vec![
                    PExpr::PtVar("P".into()),
                    PExpr::Seg2("B".into(), "C".into()),
                ],
                Value::Bool(true),
            ),
        },
        // Angle bisector theorem: BD/DC = AB/AC.
        Rule {
            id: "angle-bisector-theorem",
            antecedents: vec![
                PClaim::PredVal(
                    "isanglebisector".into(),
                    vec![
                        PExpr::Seg2("A".into(), "D".into()),
                        PExpr::Tri3("B".into(), "A".into(), "C".into()),
                    ],
                    Value::Bool(true),
                ),
                PClaim::On(PExpr::PtVar("D".into()), PExpr::Seg2("B".into(), "C".into())),
            ],
            requires: vec![],
            consequent: PClaim::RatioEq(
                PRatioExpr::Quot {
                    num: PRatioAtom::Expr(PExpr::Seg2("B".into(), "D".into())),
                    den: PRatioAtom::Expr(PExpr::Seg2("D".into(), "C".into())),
                },
                PRatioExpr::Quot {
                    num: PRatioAtom::Expr(PExpr::Seg2("A".into(), "B".into())),
                    den: PRatioAtom::Expr(PExpr::Seg2("A".into(), "C".into())),
                },
            ),
        },
        // An altitude is perpendicular to its base.
        Rule {
            id: "altitude-is-perpendicular",
            antecedents: vec![PClaim::PredVal(
                "isaltitude".into(),
                vec![
                    PExpr::Seg2("A".into(), "H".into()),
                    PExpr::Seg2("B".into(), "C".into()),
                ],
                Value::Bool(true),
            )],
            requires: vec![],
            consequent: PClaim::PredVal(
                "isperpendicular".into(),
                vec![
                    PExpr::Seg2("A".into(), "H".into()),
                    PExpr::Seg2("B".into(), "C".into()),
                ],
                Value::Bool(true),
            ),
        },
        // Mid-segment theorem: the segment joining two side midpoints is
        // parallel to the third side.
        Rule {
            id: "midsegment-parallel",
            antecedents: vec![
                PClaim::PredVal(
                    "ismedian".into(),
                    vec![PExpr::PtVar("W".into()), PExpr::Seg2("A".into(), "B".into())],
                    Value::Bool(true),
                ),
                PClaim::PredVal(
                    "ismedian".into(),
                    vec![PExpr::PtVar("Z".into()), PExpr::Seg2("A".into(), "C".into())],
                    Value::Bool(true),
                ),
            ],
            requires: vec![],
            consequent: PClaim::PredVal(
                "isparallel".into(),
                vec![
                    PExpr::Seg2("W".into(), "Z".into()),
                    PExpr::Seg2("B".into(), "C".into()),
                ],
                Value::Bool(true),
            ),
        },
        // Mid-segment theorem: the mid-segment is half the third side.
        Rule {
            id: "midsegment-half-length",
            antecedents: vec![
                PClaim::PredVal(
                    "ismedian".into(),
                    vec![PExpr::PtVar("W".into()), PExpr::Seg2("A".into(), "B".into())],
                    Value::Bool(true),
                ),
                PClaim::PredVal(
                    "ismedian".into(),
                    vec![PExpr::PtVar("Z".into()), PExpr::Seg2("A".into(), "C".into())],
                    Value::Bool(true),
                ),
            ],
            requires: vec![],
            consequent: PClaim::RatioEq(
                PRatioExpr::Quot {
                    num: PRatioAtom::Expr(PExpr::Seg2("W".into(), "Z".into())),
                    den: PRatioAtom::Expr(PExpr::Seg2("B".into(), "C".into())),
                },
                PRatioExpr::Quot {
                    num: PRatioAtom::Int(1),
                    den: PRatioAtom::Int(2),
                },
            ),
        },
        // The circumcenter is equidistant from the vertices.
        Rule {
            id: "circumcenter-equidistant-ab",
            antecedents: vec![PClaim::PredVal(
                "iscircumcenter".into(),
                vec![PExpr::PtVar("O".into()), PExpr::Tri3("A".into(), "B".into(), "C".into())],
                Value::Bool(true),
            )],
            requires: vec![],
            consequent: PClaim::SegEq(
                PExpr::Seg2("O".into(), "A".into()),
                PExpr::Seg2("O".into(), "B".into()),
            ),
        },
        Rule {
            id: "circumcenter-equidistant-ac",
            antecedents: vec![PClaim::PredVal(
                "iscircumcenter".into(),
                vec![PExpr::PtVar("O".into()), PExpr::Tri3("A".into(), "B".into(), "C".into())],
                Value::Bool(true),
            )],
            requires: vec![],
            consequent: PClaim::SegEq(
                PExpr::Seg2("O".into(), "A".into()),
                PExpr::Seg2("O".into(), "C".into()),
            ),
        },
        // The incenter lies on each angle bisector.
        Rule {
            id: "incenter-on-bisector-a",
            antecedents: vec![PClaim::PredVal(
                "isincenter".into(),
                vec![PExpr::PtVar("I".into()), PExpr::Tri3("A".into(), "B".into(), "C".into())],
                Value::Bool(true),
            )],
            requires: vec![],
            consequent: PClaim::PredVal(
                "isanglebisector".into(),
                vec![
                    PExpr::Seg2("A".into(), "I".into()),
                    PExpr::Tri3("B".into(), "A".into(), "C".into()),
                ],
                Value::Bool(true),
            ),
        },
        Rule {
            id: "incenter-on-bisector-b",
            antecedents: vec![PClaim::PredVal(
                "isincenter".into(),
                vec![PExpr::PtVar("I".into()), PExpr::Tri3("A".into(), "B".into(), "C".into())],
                Value::Bool(true),
            )],
            requires: vec![],
            consequent: PClaim::PredVal(
                "isanglebisector".into(),
                vec![
                    PExpr::Seg2("B".into(), "I".into()),
                    PExpr::Tri3("A".into(), "B".into(), "C".into()),
                ],
                Value::Bool(true),
            ),
        },
        Rule {
            id: "incenter-on-bisector-c",
            antecedents: vec![PClaim::PredVal(
                "isincenter".into(),
                vec![PExpr::PtVar("I".into()), PExpr::Tri3("A".into(), "B".into(), "C".into())],
                Value::Bool(true),
            )],
            requires: vec![],
            consequent: PClaim::PredVal(
                "isanglebisector".into(),
                vec![
                    PExpr::Seg2("C".into(), "I".into()),
                    PExpr::Tri3("A".into(), "C".into(), "B".into()),
                ],
                Value::Bool(true),
            ),
        },
        // The orthocenter lies on each altitude.
        Rule {
            id: "orthocenter-on-altitude-a",
            antecedents: vec![PClaim::PredVal(
                "isorthocenter".into(),
                vec![PExpr::PtVar("H".into()), PExpr::Tri3("A".into(), "B".into(), "C".into())],
                Value::Bool(true),
            )],
            requires: vec![],
            consequent: PClaim::PredVal(
                "isperpendicular".into(),
                vec![
                    PExpr::Seg2("A".into(), "H".into()),
                    PExpr::Seg2("B".into(), "C".into()),
                ],
                Value::Bool(true),
            ),
        },
        Rule {
            id: "orthocenter-on-altitude-b",
            antecedents: vec![PClaim::PredVal(
                "isorthocenter".into(),
                vec![PExpr::PtVar("H".into()), PExpr::Tri3("A".into(), "B".into(), "C".into())],
                Value::Bool(true),
            )],
            requires: vec![],
            consequent: PClaim::PredVal(
                "isperpendicular".into(),
                vec![
                    PExpr::Seg2("B".into(), "H".into()),
                    PExpr::Seg2("A".into(), "C".into()),
                ],
                Value::Bool(true),
            ),
        },
        Rule {
            id: "orthocenter-on-altitude-c",
            antecedents: vec![PClaim::PredVal(
                "isorthocenter".into(),
                vec![PExpr::PtVar("H".into()), PExpr::Tri3("A".into(), "B".into(), "C".into())],
                Value::Bool(true),
            )],
            requires: vec![],
            consequent: PClaim::PredVal(
                "isperpendicular".into(),
                vec![
                    PExpr::Seg2("C".into(), "H".into()),
                    PExpr::Seg2("A".into(), "B".into()),
                ],
                Value::Bool(true),
            ),
        },
        // The centroid lies on each median.
        Rule {
            id: "centroid-on-median-a",
            antecedents: vec![
                PClaim::PredVal(
                    "iscentroid".into(),
                    vec![PExpr::PtVar("G".into()), PExpr::Tri3("A".into(), "B".into(), "C".into())],
                    Value::Bool(true),
                ),
                PClaim::PredVal(
                    "ismedian".into(),
                    vec![PExpr::PtVar("D".into()), PExpr::Seg2("B".into(), "C".into())],
                    Value::Bool(true),
                ),
            ],
            requires: vec![],
            consequent: PClaim::On(
                PExpr::PtVar("G".into()),
                PExpr::Seg2("A".into(), "D".into()),
            ),
        },
        Rule {
            id: "centroid-on-median-b",
            antecedents: vec![
                PClaim::PredVal(
                    "iscentroid".into(),
                    vec![PExpr::PtVar("G".into()), PExpr::Tri3("A".into(), "B".into(), "C".into())],
                    Value::Bool(true),
                ),
                PClaim::PredVal(
                    "ismedian".into(),
                    vec![PExpr::PtVar("E".into()), PExpr::Seg2("C".into(), "A".into())],
                    Value::Bool(true),
                ),
            ],
            requires: vec![],
            consequent: PClaim::On(
                PExpr::PtVar("G".into()),
                PExpr::Seg2("B".into(), "E".into()),
            ),
        },
        Rule {
            id: "centroid-on-median-c",
            antecedents: vec![
                PClaim::PredVal(
                    "iscentroid".into(),
                    vec![PExpr::PtVar("G".into()), PExpr::Tri3("A".into(), "B".into(), "C".into())],
                    Value::Bool(true),
                ),
                PClaim::PredVal(
                    "ismedian".into(),
                    vec![PExpr::PtVar("F".into()), PExpr::Seg2("A".into(), "B".into())],
                    Value::Bool(true),
                ),
            ],
            requires: vec![],
            consequent: PClaim::On(
                PExpr::PtVar("G".into()),
                PExpr::Seg2("C".into(), "F".into()),
            ),
        },
        // Thales: a line parallel to the third side cuts the other two sides
        // proportionally.
        Rule {
            id: "thales",
            antecedents: vec![
                PClaim::On(PExpr::PtVar("D".into()), PExpr::Seg2("A".into(), "B".into())),
                PClaim::On(PExpr::PtVar("E".into()), PExpr::Seg2("A".into(), "C".into())),
                PClaim::PredVal(
                    "isparallel".into(),
                    vec![
                        PExpr::Seg2("D".into(), "E".into()),
                        PExpr::Seg2("B".into(), "C".into()),
                    ],
                    Value::Bool(true),
                ),
            ],
            requires: vec![],
            consequent: PClaim::RatioEq(
                PRatioExpr::Quot {
                    num: PRatioAtom::Expr(PExpr::Seg2("A".into(), "D".into())),
                    den: PRatioAtom::Expr(PExpr::Seg2("D".into(), "B".into())),
                },
                PRatioExpr::Quot {
                    num: PRatioAtom::Expr(PExpr::Seg2("A".into(), "E".into())),
                    den: PRatioAtom::Expr(PExpr::Seg2("E".into(), "C".into())),
                },
            ),
        },
        // Converse of Thales: proportional cuts imply the joining segment is
        // parallel to the third side.
        Rule {
            id: "invthales",
            antecedents: vec![
                PClaim::On(PExpr::PtVar("D".into()), PExpr::Seg2("A".into(), "B".into())),
                PClaim::On(PExpr::PtVar("E".into()), PExpr::Seg2("A".into(), "C".into())),
                PClaim::RatioEq(
                    PRatioExpr::Quot {
                        num: PRatioAtom::Expr(PExpr::Seg2("A".into(), "D".into())),
                        den: PRatioAtom::Expr(PExpr::Seg2("D".into(), "B".into())),
                    },
                    PRatioExpr::Quot {
                        num: PRatioAtom::Expr(PExpr::Seg2("A".into(), "E".into())),
                        den: PRatioAtom::Expr(PExpr::Seg2("E".into(), "C".into())),
                    },
                ),
            ],
            requires: vec![],
            consequent: PClaim::PredVal(
                "isparallel".into(),
                vec![
                    PExpr::Seg2("D".into(), "E".into()),
                    PExpr::Seg2("B".into(), "C".into()),
                ],
                Value::Bool(true),
            ),
        },
        // Variant of converse Thales: if a line intersects AB at E and AC at L
        // with AE/EB = AL/LC, then the line is parallel to BC.
        Rule {
            id: "invthales-variant",
            antecedents: vec![
                PClaim::On(PExpr::PtVar("E".into()), PExpr::Seg2("A".into(), "B".into())),
                PClaim::On(PExpr::PtVar("L".into()), PExpr::Seg2("A".into(), "C".into())),
                PClaim::RatioEq(
                    PRatioExpr::Quot {
                        num: PRatioAtom::Expr(PExpr::Seg2("A".into(), "E".into())),
                        den: PRatioAtom::Expr(PExpr::Seg2("E".into(), "B".into())),
                    },
                    PRatioExpr::Quot {
                        num: PRatioAtom::Expr(PExpr::Seg2("A".into(), "L".into())),
                        den: PRatioAtom::Expr(PExpr::Seg2("L".into(), "C".into())),
                    },
                ),
            ],
            requires: vec![],
            consequent: PClaim::PredVal(
                "isparallel".into(),
                vec![
                    PExpr::Seg2("E".into(), "L".into()),
                    PExpr::Seg2("B".into(), "C".into()),
                ],
                Value::Bool(true),
            ),
        },
        // In an isosceles triangle the two legs are equal.
        Rule {
            id: "isosceles-legs-equal",
            antecedents: vec![PClaim::PredVal(
                "isisosceles".into(),
                vec![PExpr::AnyRef("T".into())],
                Value::Bool(true),
            )],
            requires: vec![PClaim::IsoscelesAt(
                PExpr::AnyRef("T".into()),
                PExpr::PtVar("A".into()),
            )],
            consequent: PClaim::SegEq(
                PExpr::Seg2("A".into(), "B".into()),
                PExpr::Seg2("A".into(), "C".into()),
            ),
        },
        // In an isosceles triangle the apex median is also the angle bisector.
        Rule {
            id: "isosceles-apex-median-bisector",
            antecedents: vec![
                PClaim::PredVal(
                    "isisosceles".into(),
                    vec![PExpr::AnyRef("T".into())],
                    Value::Bool(true),
                ),
                PClaim::PredVal(
                    "ismedian".into(),
                    vec![PExpr::PtVar("H".into()), PExpr::Seg2("B".into(), "C".into())],
                    Value::Bool(true),
                ),
            ],
            requires: vec![
                PClaim::IsoscelesAt(PExpr::AnyRef("T".into()), PExpr::PtVar("A".into())),
                PClaim::On(PExpr::PtVar("H".into()), PExpr::Seg2("B".into(), "C".into())),
            ],
            consequent: PClaim::PredVal(
                "isanglebisector".into(),
                vec![
                    PExpr::Seg2("A".into(), "H".into()),
                    PExpr::Tri3("B".into(), "A".into(), "C".into()),
                ],
                Value::Bool(true),
            ),
        },
        // A segment that is perpendicular to another, passes through its
        // midpoint, and is not the base itself is its perpendicular bisector.
        Rule {
            id: "perpendicular-bisector-def",
            antecedents: vec![
                PClaim::PredVal(
                    "isperpendicular".into(),
                    vec![
                        PExpr::Seg2("A".into(), "H".into()),
                        PExpr::Seg2("B".into(), "C".into()),
                    ],
                    Value::Bool(true),
                ),
                PClaim::On(PExpr::PtVar("H".into()), PExpr::Seg2("B".into(), "C".into())),
                PClaim::PredVal(
                    "ismedian".into(),
                    vec![PExpr::PtVar("H".into()), PExpr::Seg2("B".into(), "C".into())],
                    Value::Bool(true),
                ),
            ],
            requires: vec![],
            consequent: PClaim::PredVal(
                "isperpendicularbisector".into(),
                vec![
                    PExpr::Seg2("A".into(), "H".into()),
                    PExpr::Seg2("B".into(), "C".into()),
                ],
                Value::Bool(true),
            ),
        },
        // Isosceles triangle altitude bisects base: if ZA = ZB and ZF is
        // perpendicular to AB with F on AB, then F is the midpoint of AB.
        Rule {
            id: "iso-altitude-bisects",
            antecedents: vec![
                PClaim::SegEq(
                    PExpr::Seg2("Z".into(), "A".into()),
                    PExpr::Seg2("Z".into(), "B".into()),
                ),
                PClaim::PredVal(
                    "isperpendicular".into(),
                    vec![
                        PExpr::Seg2("Z".into(), "F".into()),
                        PExpr::Seg2("A".into(), "B".into()),
                    ],
                    Value::Bool(true),
                ),
                PClaim::On(PExpr::PtVar("F".into()), PExpr::Seg2("A".into(), "B".into())),
            ],
            requires: vec![],
            consequent: PClaim::PredVal(
                "ismedian".into(),
                vec![
                    PExpr::PtVar("F".into()),
                    PExpr::Seg2("A".into(), "B".into()),
                ],
                Value::Bool(true),
            ),
        },
        // Perpendicular from parallel: if AB || CD and EF is perpendicular to CD,
        // then AB is perpendicular to EF (parallel lines share perpendiculars).
        Rule {
            id: "perp-with-parallel",
            antecedents: vec![
                PClaim::PredVal(
                    "isparallel".into(),
                    vec![
                        PExpr::Seg2("A".into(), "B".into()),
                        PExpr::Seg2("C".into(), "D".into()),
                    ],
                    Value::Bool(true),
                ),
                PClaim::PredVal(
                    "isperpendicular".into(),
                    vec![
                        PExpr::Seg2("E".into(), "F".into()),
                        PExpr::Seg2("C".into(), "D".into()),
                    ],
                    Value::Bool(true),
                ),
            ],
            requires: vec![],
            consequent: PClaim::PredVal(
                "isperpendicular".into(),
                vec![
                    PExpr::Seg2("A".into(), "B".into()),
                    PExpr::Seg2("E".into(), "F".into()),
                ],
                Value::Bool(true),
            ),
        },
        // The circumcenter is equidistant from all vertices, so all vertices
        // lie on the same circle (the circumcircle).
        Rule {
            id: "circumcenter-equidistant-circle",
            antecedents: vec![PClaim::PredVal(
                "iscircumcenter".into(),
                vec![PExpr::PtVar("O".into()), PExpr::Tri3("A".into(), "B".into(), "C".into())],
                Value::Bool(true),
            )],
            requires: vec![],
            consequent: PClaim::OnSameCircle(vec![
                PExpr::PtVar("A".into()),
                PExpr::PtVar("B".into()),
                PExpr::PtVar("C".into()),
            ]),
        },
        // If a point is equidistant from three points, those three points
        // lie on a circle centered at that point.
        Rule {
            id: "same-circle-from-equidistant",
            antecedents: vec![
                PClaim::SegEq(
                    PExpr::Seg2("O".into(), "A".into()),
                    PExpr::Seg2("O".into(), "B".into()),
                ),
                PClaim::SegEq(
                    PExpr::Seg2("O".into(), "A".into()),
                    PExpr::Seg2("O".into(), "C".into()),
                ),
            ],
            requires: vec![],
            consequent: PClaim::OnSameCircle(vec![
                PExpr::PtVar("A".into()),
                PExpr::PtVar("B".into()),
                PExpr::PtVar("C".into()),
            ]),
        },
        // Parallel transitivity: if AB || CD and CD || EF then AB || EF.
        Rule {
            id: "parallel-transitivity",
            antecedents: vec![
                PClaim::PredVal(
                    "isparallel".into(),
                    vec![
                        PExpr::Seg2("A".into(), "B".into()),
                        PExpr::Seg2("C".into(), "D".into()),
                    ],
                    Value::Bool(true),
                ),
                PClaim::PredVal(
                    "isparallel".into(),
                    vec![
                        PExpr::Seg2("C".into(), "D".into()),
                        PExpr::Seg2("E".into(), "F".into()),
                    ],
                    Value::Bool(true),
                ),
            ],
            requires: vec![],
            consequent: PClaim::PredVal(
                "isparallel".into(),
                vec![
                    PExpr::Seg2("A".into(), "B".into()),
                    PExpr::Seg2("E".into(), "F".into()),
                ],
                Value::Bool(true),
            ),
        },
        // Reflection preserves distance to points of the mirror line: E is the
        // midpoint of HM, HE is perpendicular to the mirror AB, and E lies on
        // the mirror; then any point A of the mirror is equidistant from H
        // and its image M (the mirror is the perpendicular bisector of HM).
        Rule {
            id: "mirror-preserves-distance",
            antecedents: vec![
                PClaim::PredVal(
                    "ismedian".into(),
                    vec![PExpr::PtVar("E".into()), PExpr::Seg2("H".into(), "M".into())],
                    Value::Bool(true),
                ),
                PClaim::PredVal(
                    "isperpendicular".into(),
                    vec![
                        PExpr::Seg2("H".into(), "E".into()),
                        PExpr::Seg2("A".into(), "B".into()),
                    ],
                    Value::Bool(true),
                ),
                // The point whose distances are preserved: any point of the
                // mirror line.
                PClaim::On(
                    PExpr::PtVar("P".into()),
                    PExpr::Seg2("A".into(), "B".into()),
                ),
            ],
            requires: vec![],
            consequent: PClaim::SegEq(
                PExpr::Seg2("P".into(), "M".into()),
                PExpr::Seg2("P".into(), "H".into()),
            ),
        },
        // Mirrored form: the shared segment occupies the second slot.
        Rule {
            id: "segeq-common-transitive-rev",
            antecedents: vec![
                PClaim::SegEq(
                    PExpr::Seg2("A".into(), "B".into()),
                    PExpr::AnyRef("X".into()),
                ),
                PClaim::SegEq(
                    PExpr::Seg2("A".into(), "C".into()),
                    PExpr::AnyRef("X".into()),
                ),
            ],
            requires: vec![],
            consequent: PClaim::SegEq(
                PExpr::Seg2("A".into(), "B".into()),
                PExpr::Seg2("A".into(), "C".into()),
            ),
        },
        // Two segments equal to a common third are equal to each other.
        // Claims are stored pair-sorted, so the shared segment occupies the
        // first slot of both equalities.
        Rule {
            id: "segeq-common-transitive",
            antecedents: vec![
                PClaim::SegEq(
                    PExpr::AnyRef("X".into()),
                    PExpr::Seg2("A".into(), "B".into()),
                ),
                PClaim::SegEq(
                    PExpr::AnyRef("X".into()),
                    PExpr::Seg2("A".into(), "C".into()),
                ),
            ],
            requires: vec![],
            consequent: PClaim::SegEq(
                PExpr::Seg2("A".into(), "B".into()),
                PExpr::Seg2("A".into(), "C".into()),
            ),
        },
        // In an isosceles triangle the median to the base is also the altitude:
        // AM = AN with I the midpoint of MN implies AI perpendicular to MN.
        Rule {
            id: "isosceles-apex-median-perpendicular",
            antecedents: vec![
                PClaim::SegEq(
                    PExpr::Seg2("A".into(), "M".into()),
                    PExpr::Seg2("A".into(), "N".into()),
                ),
                PClaim::PredVal(
                    "ismedian".into(),
                    vec![PExpr::PtVar("I".into()), PExpr::Seg2("M".into(), "N".into())],
                    Value::Bool(true),
                ),
            ],
            requires: vec![],
            consequent: PClaim::PredVal(
                "isperpendicular".into(),
                vec![
                    PExpr::Seg2("A".into(), "I".into()),
                    PExpr::Seg2("M".into(), "N".into()),
                ],
                Value::Bool(true),
            ),
        },
        // Nine-point configuration: with M, N the midpoints of BH, CH and J
        // the midpoint of MN, J is the midpoint of QH where Q is the midpoint
        // of BC; in particular Q, J, H are collinear.
        Rule {
            id: "nine-point-mid-collinear",
            antecedents: vec![
                PClaim::PredVal(
                    "ismedian".into(),
                    vec![PExpr::PtVar("J".into()), PExpr::Seg2("M".into(), "N".into())],
                    Value::Bool(true),
                ),
                PClaim::PredVal(
                    "ismedian".into(),
                    vec![PExpr::PtVar("M".into()), PExpr::Seg2("B".into(), "H".into())],
                    Value::Bool(true),
                ),
                PClaim::PredVal(
                    "ismedian".into(),
                    vec![PExpr::PtVar("N".into()), PExpr::Seg2("C".into(), "H".into())],
                    Value::Bool(true),
                ),
            ],
            requires: vec![
                PClaim::PredVal(
                    "ismedian".into(),
                    vec![PExpr::PtVar("Q".into()), PExpr::Seg2("B".into(), "C".into())],
                    Value::Bool(true),
                ),
            ],
            consequent: PClaim::PredVal(
                "iscollinear".into(),
                vec![
                    PExpr::PtVar("Q".into()),
                    PExpr::PtVar("J".into()),
                    PExpr::PtVar("H".into()),
                ],
                Value::Bool(true),
            ),
        },
        // Thales' circle theorem: the vertices of a right triangle are
        // concyclic (the hypotenuse is a diameter of the circumcircle).
        Rule {
            id: "right-angle-concyclic",
            antecedents: vec![PClaim::PredVal(
                "isright".into(),
                vec![PExpr::Tri3("A".into(), "B".into(), "C".into())],
                Value::Bool(true),
            )],
            requires: vec![PClaim::PredAt(
                "rightat".into(),
                vec![PExpr::Tri3("A".into(), "B".into(), "C".into())],
                PExpr::PtVar("A".into()),
            )],
            consequent: PClaim::OnSameCircle(vec![
                PExpr::PtVar("A".into()),
                PExpr::PtVar("B".into()),
                PExpr::PtVar("C".into()),
            ]),
        },
    ]
}



