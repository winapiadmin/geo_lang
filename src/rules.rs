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
    /// Fallback proof chain template used when this rule is disabled.
    /// Format: `"step1 [rule1] -> step2 [rule2] -> ..."` where each step
    /// can reference variables bound by the rule's antecedent matching.
    pub chain: Option<&'static str>,
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
            // Handle legacy 2-char segments ("ab"), multi-char with delimiter
            // ("p1-p2"), and bare segment references from ratios ("jk1").
            let pairs: Vec<(String, String)> = if refval.contains('-') {
                let parts: Vec<&str> = refval.split('-').collect();
                if parts.len() == 2 {
                    vec![(parts[0].to_string(), parts[1].to_string())]
                } else {
                    return vec![];
                }
            } else if refval.len() == 2 {
                vec![(refval[0..1].to_string(), refval[1..2].to_string())]
            } else {
                // Bare reference like "jk1" — try every split position.
                let mut v = Vec::new();
                for i in 1..refval.len() {
                    v.push((refval[..i].to_string(), refval[i..].to_string()));
                }
                v
            };
            let mut out = Vec::new();
            for (a, b) in &pairs {
                if let Some(fb) = try_bind(v1, a, bind).into_iter().next() {
                    out.extend(try_bind(v2, b, &fb));
                }
                if let Some(fb) = try_bind(v1, b, bind).into_iter().next() {
                    out.extend(try_bind(v2, a, &fb));
                }
            }
            out
        }
        PExpr::Tri3(v1, v2, v3) => {
            let mut pts = Vec::new();
            let mut i = 0;
            while i < refval.len() {
                let start = i;
                if !refval[i..].chars().next().unwrap().is_ascii_alphabetic() {
                    i += 1;
                    continue;
                }
                i += 1;
                while i < refval.len() && refval[i..].chars().next().unwrap().is_ascii_digit() {
                    i += 1;
                }
                pts.push(refval[start..i].to_string());
            }
            if pts.len() == 3 {
                let mut out = Vec::new();
                let mut perm = pts.clone();
                permute(&mut perm, 0, &mut |perm| {
                    let mut cur = vec![bind.clone()];
                    for (var, pt) in [(v1, &perm[0]), (v2, &perm[1]), (v3, &perm[2])] {
                        let mut next = Vec::new();
                        for b in &cur {
                            next.extend(try_bind(var, pt, b));
                        }
                        cur = next;
                        if cur.is_empty() {
                            return;
                        }
                    }
                    out.extend(cur);
                });
                out
            } else if refval.len() == 3 {
                let a = refval[0..1].to_string();
                let b = refval[1..2].to_string();
                let c = refval[2..3].to_string();
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

/// Generate all permutations of `xs[start..]`, calling `f` for each.
fn permute(xs: &mut Vec<String>, start: usize, f: &mut dyn FnMut(&[String])) {
    if start >= xs.len() {
        f(xs);
        return;
    }
    for i in start..xs.len() {
        xs.swap(start, i);
        permute(xs, start + 1, f);
        xs.swap(start, i);
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
        ) if crate::claim::normalize_pred_name(name) == crate::claim::normalize_pred_name(pn) && value == pv && args.len() == pargs.len() => {
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
                    "isparallel" | "isperpendicular" | "isequal" | "equals" | "issimilar"
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
            // `iscollinear`'s claim args are stored alphabetically sorted
            // (see `Claim::pred`), so the argument at a given position may
            // not correspond to the same pattern variable at that position
            // — e.g. `IsCollinear(Q,J,H)` is actually stored as `(H,J,Q)`.
            // Try every permutation of the 3 args against the pattern's 3
            // slots so a rule written positionally (like the fallback chain
            // in `on-segment-implies-collinear` / `nine-point-mid-collinear`)
            // still matches the sorted fact.
            if args.len() == 3 && name == "iscollinear" {
                const PERMS: [[usize; 3]; 5] =
                    [[0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]];
                for perm in PERMS.iter() {
                    let mut cur = vec![bind.clone()];
                    for i in 0..3 {
                        let mut next = Vec::new();
                        for b in &cur {
                            next.extend(match_expr(&args[perm[i]], &pargs[i], b));
                        }
                        cur = next;
                    }
                    out.extend(cur);
                }
            }
            out
        }
        (
            Claim::PredVal { name, args, value },
            PClaim::PredAt(pn, pargs, pe),
        ) if crate::claim::normalize_pred_name(name) == crate::claim::normalize_pred_name(pn) && args.len() == pargs.len() => {
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
            // Try all permutations so sorted OnSameCircle facts can match
            // rules that assume a specific geometric ordering (e.g. diameter
            // endpoints at specific positions).
            let mut out = Vec::new();
            let mut perm = pts.clone();
            permute(&mut perm, 0, &mut |perm| {
                let mut cur = vec![bind.clone()];
                for (pt, pp) in perm.iter().zip(pps.iter()) {
                    let mut next = Vec::new();
                    for b in &cur {
                        next.extend(match_expr(pt, pp, b));
                    }
                    cur = next;
                    if cur.is_empty() {
                        return;
                    }
                }
                out.extend(cur);
            });
            out
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
        PExpr::PtVar(v) => bind.get(v).cloned().unwrap_or_default(),
        // An unbound AnyRef is a literal (e.g. `sin(ABC)` in a ratio
        // consequent): keep the pattern text so instantiate does not drop it.
        PExpr::AnyRef(v) => bind.get(v).cloned().unwrap_or_else(|| v.clone()),
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
            Claim::pred(name, &args, value.clone())
        }
        PClaim::PredAt(name, args, pe) => {
            let args: Vec<String> = args.iter().map(|a| render_expr(a, bind)).collect();
            let p = render_expr(pe, bind);
            Claim::pred(name, &args, Value::Point(p))
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


/// Load geometry rules from .geo files in the rules/ directory.
pub fn rule_base() -> Vec<Rule> {
    let path = std::path::Path::new("rules");
        crate::rule_loader::load_rules_from_dir(path).unwrap_or_else(|e| {
        eprintln!("// Error loading rules: {}", e);
        Vec::new()
    })
}
pub fn derive_all(chain: &[Claim], _hints: &[&str]) -> Vec<Claim> {
    let rules = rule_base();
    let mut out = Vec::new();
    for rule in &rules {
        let mut cur: Vec<Bindings> = vec![Bindings::new()];
        for ant in &rule.antecedents {
            let mut next = Vec::new();
            for bind in &cur {
                for fact in chain {
                    next.extend(match_pat(fact, ant, bind));
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
                let inst = instantiate(req, &bind);
                if inst.has_unbound() || !chain.contains(&inst) {
                    ok = false;
                    break;
                }
            }
            if !ok {
                continue;
            }
            let c = instantiate(&rule.consequent, &bind);
            if !c.has_unbound() && !chain.contains(&c) {
                out.push(c);
            }
        }
    }
    out
}
