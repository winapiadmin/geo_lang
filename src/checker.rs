//! Proof checker: builds the fact store from the input section and validates
//! every proof block, producing diagnostics in the style of the language spec.

use crate::ast::{ClaimExpr, File, Geom, InputStmt, LenExpr, RadiusSpec, Scope, Step};
use crate::claim::{Claim, RatioAtom, RatioExpr, Value};
use crate::diag::{Diagnostic, Span};
use crate::rules::{apply_rule, derive_all, find_hint, rule_base};
use std::collections::HashMap;

/// Where a fact was established.
#[derive(Debug, Clone)]
pub enum Origin {
    Input,
    #[allow(dead_code)]
    Proof(u32, usize),
}

#[derive(Debug, Clone)]
pub struct Fact {
    #[allow(dead_code)]
    pub claim: Claim,
    pub origin: Origin,
}

/// A store of established facts.
#[derive(Debug, Default, Clone)]
pub struct FactStore {
    map: HashMap<Claim, Fact>,
}

impl FactStore {
    pub fn new() -> FactStore {
        FactStore { map: HashMap::new() }
    }

    pub fn contains(&self, c: &Claim) -> bool {
        self.map.contains_key(c)
    }

    /// Add a fact. Returns `false` (and keeps the original) if already present.
    pub fn add(&mut self, claim: Claim, origin: Origin) -> bool {
        if self.map.contains_key(&claim) {
            false
        } else {
            self.map.insert(claim.clone(), Fact { claim, origin });
            true
        }
    }

    pub fn get(&self, c: &Claim) -> Option<&Fact> {
        self.map.get(c)
    }

    pub fn all(&self) -> Vec<Claim> {
        self.map.keys().cloned().collect()
    }
}

/// Convert a claim expression into its atomic claims.
pub fn claim_atoms(expr: &ClaimExpr) -> Vec<Claim> {
    match expr {
        ClaimExpr::EqChain { items, .. } => {
            let mut out = Vec::new();
            for pair in items.windows(2) {
                let l = &pair[0];
                let r = &pair[1];
                if let Some(n) = l.numeric() {
                    let n_u32 = n.round() as u32;
                    // `<number> = <len>`: the numeric side is on the left.
                    // Only create a fact for simple numeric literals; compound
                    // expressions (Div, Sqrt, Sq, etc.) that aren't integers
                    // lose precision when rounded to u32 (e.g. 30/7 → 4).
                    let lhs_is_literal = matches!(l, LenExpr::Num(..));
                    let is_integer = (n - n_u32 as f64).abs() < 1e-9;
                    if lhs_is_literal || is_integer {
                        if r.squared() {
                            out.push(Claim::sq_eq(&r.seg(), n_u32));
                        } else if matches!(r, LenExpr::Seg(..) | LenExpr::Distance(..)) {
                            out.push(Claim::len_eq(&r.seg(), n_u32));
                        }
                    }
                    // Trig values (sin/cos/tan) produce non-integer values;
                    // don't create LenEq — they're verified numerically.
                } else if let Some(n) = r.numeric() {
                    // `<len> = <number>`: a numeric length fact.
                    // Only produce a LenEq when the RHS is a simple numeric
                    // literal — compound expressions (Div, Add, etc.) lose
                    // precision when rounded to u32 (e.g. AE=30/7 → 4).
                    let rhs_is_literal = matches!(r, LenExpr::Num(..));
                    if rhs_is_literal {
                        if l.squared() {
                            out.push(Claim::sq_eq(&l.seg(), n.round() as u32));
                        } else if matches!(l, LenExpr::Seg(..) | LenExpr::Distance(..)) {
                            out.push(Claim::len_eq(&l.seg(), n.round() as u32));
                        }
                    }
                    // Trig values (sin/cos/tan) produce non-integer values;
                    // don't create LenEq — they're verified numerically.
                } else if l.squared() && r.squared() {
                    // `X^2 = Y^2`: equal squared lengths imply equal lengths
                    // (distances are nonnegative).
                    out.push(Claim::seg_eq(&l.seg(), &r.seg()));
                } else {
                    // When either side is an arithmetic expression (Add/Sub/Mul),
                    // don't produce a SegEq — it would lose information.
                    // These are handled by numeric verification in process_chain.
                    let has_arith = matches!(l, LenExpr::Add(..) | LenExpr::Sub(..) | LenExpr::Mul(..) | LenExpr::Div(..) | LenExpr::Sqrt(..) | LenExpr::Sq(..))
                        || matches!(r, LenExpr::Add(..) | LenExpr::Sub(..) | LenExpr::Mul(..) | LenExpr::Div(..) | LenExpr::Sqrt(..) | LenExpr::Sq(..));
                    if !has_arith {
                        out.push(Claim::seg_eq(&l.seg(), &r.seg()));
                    }
                }
            }
            out
        }
        ClaimExpr::PredEq { name, args, value, .. } => {
            vec![Claim::pred(name, args, value.clone())]
        }
        ClaimExpr::PredCall { name, args, .. } => {
            vec![Claim::pred(name, args, Value::Bool(true))]
        }
        ClaimExpr::Conj { items, .. } => {
            let mut out = Vec::new();
            for it in items {
                out.extend(claim_atoms(it));
            }
            out
        }
        ClaimExpr::TriEq { lhs, rhs, .. } => vec![Claim::tri_eq(lhs, rhs)],
        ClaimExpr::TriCall { lhs, rhs, .. } => vec![Claim::tri_eq(lhs, rhs)],
        ClaimExpr::AngleEq { lhs, rhs, .. } => vec![Claim::angle_eq(lhs, rhs)],
        ClaimExpr::RatioEq { lhs, rhs, .. } => vec![Claim::ratio_eq(lhs, rhs)],
        // Sums are verified numerically by the prover, not as atomic facts.
        ClaimExpr::Sum { .. } => vec![],
    }
}

/// True if an equality chain compares a squared length with a plain one,
/// e.g. `BD^2 = CE`, which is a unit mismatch.
fn eq_chain_mixed(items: &[LenExpr]) -> bool {
    // Only flag truly mixed chains where one side is a plain segment and
    // the other is a bare `^2` — compound expressions (Add/Sub/Mul/Sqrt/Trig)
    // may evaluate to squared lengths (e.g. law of cosines).
    fn is_plain(e: &LenExpr) -> bool {
        matches!(e, LenExpr::Seg(_) | LenExpr::Distance(_, _))
    }
    fn is_bare_sq(e: &LenExpr) -> bool {
        match e {
            LenExpr::Sq(inner) => is_plain(inner.as_ref()),
            _ => false,
        }
    }
    items.windows(2).any(|w| {
        let (l, r) = (&w[0], &w[1]);
        (is_plain(l) && is_bare_sq(r)) || (is_bare_sq(l) && is_plain(r))
    })
}

/// Levenshtein edit distance between two strings.
fn edit_distance(a: &str, b: &str) -> usize {
    let a: Vec<char> = a.chars().collect();
    let b: Vec<char> = b.chars().collect();
    let m = a.len();
    let n = b.len();
    let mut dp = vec![vec![0usize; n + 1]; m + 1];
    for i in 0..=m { dp[i][0] = i; }
    for j in 0..=n { dp[0][j] = j; }
    for i in 1..=m {
        for j in 1..=n {
            let cost = if a[i - 1] == b[j - 1] { 0 } else { 1 };
            dp[i][j] = std::cmp::min(
                std::cmp::min(dp[i - 1][j] + 1, dp[i][j - 1] + 1),
                dp[i - 1][j - 1] + cost,
            );
        }
    }
    dp[m][n]
}

/// Known predicate names (lowercase).
const KNOWN_PREDS: &[&str] = &[
    "isisosceles", "isacute", "isobtuse", "isright", "ismedian",
    "issimilar", "isperpendicular", "isparallel", "isanglebisector",
    "isaltitude", "iscircumcenter", "isincenter", "isorthocenter",
    "iscentroid", "isperpendicularbisector", "isnone", "isoscelesat",
    "on", "onsamecircle", "oncircle", "iscirclecenter", "isrectangle",
    "intersection",
    "equals", "rightat",
];

/// If `name` is not a known predicate, suggest the closest match.
/// Uses edit distance ≤ 5, or strips common suffixes (Line, Bisector) and
/// retries with a tighter threshold (for `IsPrependicularLine` → `IsPerpendicular`).
/// Returns `None` if the name is already known.
fn suggest_predicate(name: &str) -> Option<String> {
    let low = name.to_lowercase();
    if KNOWN_PREDS.contains(&low.as_str()) {
        return None;
    }
    // Try edit distance directly.
    let mut best: Option<(&str, usize)> = None;
    for &known in KNOWN_PREDS {
        let d = edit_distance(&low, known);
        if d <= 5 {
            match best {
                None => best = Some((known, d)),
                Some((_, bd)) if d < bd => best = Some((known, d)),
                _ => {}
            }
        }
    }
    // Strip known suffixes and retry with threshold 3.
    // e.g. "isprependicularline" → strip "line" → "isprependicular" → distance 1 from "isperpendicular".
    if best.is_none() || best.unwrap().1 > 3 {
        for suffix in &["line", "bisector"] {
            if low.ends_with(suffix) {
                let stripped = &low[..low.len() - suffix.len()];
                if stripped.len() >= 5 {
                    for &known in KNOWN_PREDS {
                        let d = edit_distance(stripped, known);
                        if d <= 3 {
                            match &best {
                                None => best = Some((known, d)),
                                Some((_, bd)) if d < *bd => best = Some((known, d)),
                                _ => {}
                            }
                        }
                    }
                }
            }
        }
    }
    best.map(|(k, _)| crate::claim::display_predicate(k))
}

fn span_of(pos: crate::ast::Pos, len: usize) -> Span {
    Span { line: pos.line, col: pos.col, len }
}

fn len_expr_len(e: &LenExpr) -> usize {
    match e {
        LenExpr::Seg(r) => r.len(),
        LenExpr::Distance(a, b) => "Distance".len() + 1 + a.len() + 1 + b.len() + 1,
        LenExpr::Num(n) => n.to_string().len(),
        LenExpr::Sq(inner) => len_expr_len(inner) + 2,
        LenExpr::Sqrt(inner) => 5 + len_expr_len(inner) + 1,
        LenExpr::Add(l, r) => len_expr_len(l) + 1 + len_expr_len(r),
        LenExpr::Sub(l, r) => len_expr_len(l) + 1 + len_expr_len(r),
        LenExpr::Mul(l, r) => len_expr_len(l) + 1 + len_expr_len(r),
        LenExpr::Div(l, r) => len_expr_len(l) + 1 + len_expr_len(r),
        LenExpr::Trig(func, angle) => func.len() + 1 + angle.len() + 1,
    }
}

/// Convert an expression into the diagnostic underline length.
fn expr_len(expr: &ClaimExpr) -> usize {
    match expr {
        ClaimExpr::EqChain { items, .. } => {
            items.iter().map(len_expr_len).sum::<usize>() + (items.len() - 1)
        }
        ClaimExpr::Sum { lhs, rhs, .. } => {
            let term_len = |t: &crate::ast::SumTerm| -> usize {
                t.len.as_ref().map(len_expr_len).unwrap_or(3)
                    + t.cos_angle.as_ref().map(|a| a.len() + 4).unwrap_or(0)
                    + 1
            };
            let total: usize =
                lhs.iter().map(&term_len).sum::<usize>() + rhs.iter().map(&term_len).sum::<usize>();
            total
        }
        ClaimExpr::PredEq { name, args, value, .. } => {
            let args_len: usize =
                args.iter().map(|a| a.len()).sum::<usize>() + args.len().saturating_sub(1);
            name.len() + 1 + args_len + 1 + 1 + value.render().len()
        }
        ClaimExpr::PredCall { name, args, .. } => {
            let args_len: usize =
                args.iter().map(|a| a.len()).sum::<usize>() + args.len().saturating_sub(1);
            name.len() + 1 + args_len + 1
        }
        ClaimExpr::Conj { items, .. } => {
            let mut n = 1;
            for (i, it) in items.iter().enumerate() {
                if i > 0 {
                    n += 4;
                }
                n += expr_len(it);
            }
            n
        }
        ClaimExpr::TriEq { lhs, rhs, .. } => lhs.len() + 1 + rhs.len(),
        ClaimExpr::TriCall { lhs, rhs, .. } => {
            "Triangle(".len() + lhs.len() + 1 + 1 + "Triangle(".len() + rhs.len() + 1
        }
        ClaimExpr::AngleEq { lhs, rhs, .. } => {
            "Angle(".len() + lhs.len() + 1 + 1 + "Angle(".len() + rhs.len() + 1
        }
        ClaimExpr::RatioEq { lhs, rhs, .. } => {
            ratio_expr_len(lhs) + 1 + ratio_expr_len(rhs)
        }
    }
}

fn ratio_atom_len(a: &RatioAtom) -> usize {
    match a {
        RatioAtom::Seg(s) => s.len(),
        RatioAtom::Int(n) => n.to_string().len(),
    }
}

fn ratio_expr_len(e: &RatioExpr) -> usize {
    match e {
        RatioExpr::Seg(s) => s.len(),
        RatioExpr::Quot { num, den } => ratio_atom_len(num) + 1 + ratio_atom_len(den),
    }
}

/// Apply a batch of input statements (e.g. a goal's scoped `inp[N]:`
/// section) to an existing fact store.
pub fn apply_input_statements(facts: &mut FactStore, stmts: &[&InputStmt]) {
    let known = std::collections::HashMap::new();
    let circles = std::collections::HashMap::new();
    for stmt in stmts {
        process_input(stmt, facts, &mut Vec::new(), &known, &circles);
    }
    derive_global_facts(facts);
    derive_perpendicular_foot_midpoints(facts);
}

/// Display string for a length expression (used by Calc goals).
pub fn atom_display_len(e: &LenExpr) -> String {
    render_len_expr(e)
}

/// Build the fact store from only the input section (used by the prover).
pub fn build_facts_from_input(file: &File) -> FactStore {
    let mut facts = FactStore::new();
    let mut diags = Vec::new();
    let known = known_perp_lines(file);
    let circles = known_circles(file);
    for stmt in &file.input {
        process_input(stmt, &mut facts, &mut diags, &known, &circles);
    }
    derive_global_facts(&mut facts);
    facts
}

/// Run the global fact-derivation pipeline (transitive closures, geometric
/// property derivation, segment-equality and circle-membership closures) over
/// a fact store built from a file's `inp:` section. Shared by the prover and
/// the checker so both reason over the same derived facts.
pub fn derive_global_facts(facts: &mut FactStore) {
    // Transitive closure for On facts: if X on YZ and Z on AB, then X on AB
    transitive_on_closure(facts);
    // Thales: the midpoint of the hypotenuse of a right triangle is
    // equidistant from all three vertices.
    derive_right_triangle_circumcenter(facts);
    // In a rectangle the diagonals bisect each other: their intersection
    // point is the midpoint of both diagonals, the diagonals are equal, so
    // the midpoint is equidistant from all four vertices (the circumcenter)
    // and the four vertices are concyclic.
    derive_rectangle_properties(facts);
    // Length-equality closure + circle-membership propagation.
    seg_eq_closure(facts);
    circle_membership_closure(facts);
}


/// Transitive closure of segment-equality facts via union-find: if AB=CD and
/// CD=EF are known, materialize AB=EF (bounded per equivalence class).
pub fn seg_eq_closure(facts: &mut FactStore) {
    const MAX_GROUP: usize = 24;
    let eqs: Vec<(String, String)> = facts
        .all()
        .into_iter()
        .filter_map(|c| match c {
            Claim::SegEq(a, b) => Some((a.clone(), b.clone())),
            Claim::RadiusEq(k, side) => {
                // Sentinel node keeps circle radii in the same length graph.
                Some((format!("radius:{}", k), side.clone()))
            }
            _ => None,
        })
        .collect();
    if eqs.is_empty() {
        return;
    }
    let mut parent: std::collections::HashMap<String, String> = std::collections::HashMap::new();
    let find = |parent: &std::collections::HashMap<String, String>, mut x: String| -> String {
        while let Some(p) = parent.get(&x) {
            if p == &x {
                break;
            }
            x = p.clone();
        }
        x
    };
    let union = |parent: &mut std::collections::HashMap<String, String>, a: String, b: String| {
        let ra = find(parent, a);
        let rb = find(parent, b);
        if ra != rb {
            parent.insert(ra, rb);
        }
    };
    for (a, b) in &eqs {
        union(&mut parent, a.clone(), b.clone());
    }
    // Group members by root.
    let mut groups: std::collections::HashMap<String, Vec<String>> =
        std::collections::HashMap::new();
    for (a, b) in &eqs {
        for side in [a, b] {
            let r = find(&parent, side.clone());
            let g = groups.entry(r).or_default();
            if !g.contains(side) {
                g.push(side.clone());
            }
        }
    }
    // Materialize pairwise equalities within each (capped) group.
    let mut added = Vec::new();
    for members in groups.values() {
        if members.len() > MAX_GROUP {
            continue;
        }
        for i in 0..members.len() {
            for j in (i + 1)..members.len() {
                let claim = Claim::seg_eq(&members[i], &members[j]);
                if !facts.contains(&claim) {
                    added.push(claim);
                }
            }
        }
    }
    for c in added {
        facts.add(c, Origin::Input);
    }
}

/// Propagate circle membership: if P lies on declared circle K with center O,
/// and OQ is length-equal (transitively) to OP, then Q lies on K too.
pub fn circle_membership_closure(facts: &mut FactStore) {
    use std::collections::HashMap;
    // Centers: k -> o
    let centers: HashMap<String, String> = facts
        .all()
        .into_iter()
        .filter_map(|c| match c {
            Claim::PredVal { name, args, value }
                if name == "iscirclecenter" && value == Value::Bool(true) && args.len() == 2 =>
            {
                Some((args[0].clone(), args[1].clone()))
            }
            _ => None,
        })
        .collect();
    if centers.is_empty() {
        return;
    }
    // Memberships: k -> points P with OnCircle(P,k).
    let mut members: HashMap<String, Vec<String>> = HashMap::new();
    for c in facts.all() {
        if let Claim::PredVal { name, args, value } = c {
            if name == "oncircle" && value == Value::Bool(true) && args.len() == 2 {
                if centers.contains_key(&args[1]) {
                    let m = members.entry(args[1].clone()).or_default();
                    if !m.contains(&args[0]) {
                        m.push(args[0].clone());
                    }
                }
            }
        }
    }
    if members.is_empty() {
        return;
    }
    // All known points (from On facts).
    let mut points: Vec<String> = Vec::new();
    for c in facts.all() {
        if let Claim::On(p, _) = c {
            if !points.contains(&p) {
                points.push(p.clone());
            }
        }
    }
    // Length-equality adjacency: side-string -> partner strings.
    let mut adj: HashMap<String, Vec<String>> = HashMap::new();
    for c in facts.all() {
        match c {
            Claim::SegEq(a, b) => {
                adj.entry(a.clone()).or_default().push(b.clone());
                adj.entry(b.clone()).or_default().push(a.clone());
            }
            // radius:K is reachable from every length equal to the radius.
            Claim::RadiusEq(k, side) => {
                let node = format!("radius:{}", k);
                adj.entry(node.clone()).or_default().push(side.clone());
                adj.entry(side.clone()).or_default().push(node);
            }
            _ => {}
        }
    }
    // Reachable lengths from a given segment string (BFS, capped).
    fn reachable(
        start: &str,
        adj: &HashMap<String, Vec<String>>,
    ) -> std::collections::HashSet<String> {
        let mut seen = std::collections::HashSet::new();
        let mut queue = std::collections::VecDeque::new();
        seen.insert(start.to_string());
        queue.push_back(start.to_string());
        while let Some(cur) = queue.pop_front() {
            if let Some(partners) = adj.get(&cur) {
                for p in partners {
                    if seen.insert(p.clone()) && seen.len() < 64 {
                        queue.push_back(p.clone());
                    }
                }
            }
        }
        seen
    }

    let mut changed = true;
    let mut rounds = 0;
    while changed && rounds < 8 {
        changed = false;
        for k in members.keys().cloned().collect::<Vec<String>>() {
            let ps = members[&k].clone();
            let o = centers[&k].clone();
            for p in &ps {
                let sp = Claim::seg_key(&o, p);
                let reach = reachable(&sp, &adj);
                for q in &points {
                    if q == p {
                        continue;
                    }
                    let sq = Claim::seg_key(&o, q);
                    if reach.contains(&sq) {
                        let g = members.entry(k.clone()).or_default();
                        if !g.contains(q) {
                            g.push(q.clone());
                            facts.add(Claim::on_circle(q, &k), Origin::Input);
                            changed = true;
                        }
                    }
                }
            }
        }
        rounds += 1;
    }
}

/// For every right triangle `T` with `rightAt = V` and every midpoint `W` of
/// the side opposite `V`, add `WV' = WV''` for the two legs — i.e. record
/// that `W` is equidistant from all three vertices.
fn derive_right_triangle_circumcenter(facts: &mut FactStore) {
    use crate::claim::Value;
    // Collect right-triangle centers first to avoid borrowing conflicts.
    let mut rights: Vec<(String, char)> = Vec::new(); // (tri, apex)
    for c in facts.all() {
        if let Claim::PredVal { name, args, value } = c {
            if name == "rightat" && args.len() == 1 {
                if let Value::Point(p) = value {
                    let mut chars = p.chars();
                    if let (Some(ch), None) = (chars.next(), chars.next()) {
                        rights.push((args[0].clone(), ch));
                    }
                }
            }
        }
    }
    let medians: Vec<_> = facts
        .all()
        .into_iter()
        .filter_map(|c| match c {
            Claim::PredVal { name, args, value }
                if name == "ismedian" && value == Value::Bool(true) && args.len() == 2 =>
            {
                Some((args[0].clone(), args[1].clone()))
            }
            _ => None,
        })
        .collect();

    for (tri, apex) in rights {
        let tri_chars: Vec<char> = tri.chars().collect();
        if tri_chars.len() != 3 || !tri_chars.contains(&apex) {
            continue;
        }
        let others: Vec<char> = tri_chars.iter().copied().filter(|&c| c != apex).collect();
        if others.len() != 2 {
            continue;
        }
        let hyp = Claim::seg_key(&others[0].to_string(), &others[1].to_string());
        for (mid, seg) in &medians {
            if *seg == hyp {
                let a = Claim::seg_key(mid, &apex.to_string());
                let b = Claim::seg_key(mid, &others[0].to_string());
                let c2 = Claim::seg_key(mid, &others[1].to_string());
                facts.add(Claim::seg_eq(&a, &b), Origin::Input);
                facts.add(Claim::seg_eq(&a, &c2), Origin::Input);
            }
        }
    }
}

/// In a rectangle `IsRectangle(A,B,C,D)` (vertices in order) the diagonals
/// `AC` and `BD` bisect each other at their intersection. Derive:
///   * the intersection point `E` is the midpoint of both diagonals,
///   * the diagonals are equal, so `E` is equidistant from all four vertices,
///   * the four vertices are concyclic (the rectangle's circumcircle).
fn derive_rectangle_properties(facts: &mut FactStore) {
    use crate::claim::Value;
    let mut rects: Vec<(String, String, String, String)> = Vec::new();
    for c in facts.all() {
        if let Claim::PredVal { name, args, value } = c {
            if name.eq_ignore_ascii_case("rectangle")
                && args.len() == 4
                && value == Value::Bool(true)
            {
                let pts: Vec<String> = args.iter().map(|p| Claim::norm_ref(p)).collect();
                rects.push((pts[0].clone(), pts[1].clone(), pts[2].clone(), pts[3].clone()));
            }
        }
    }
    let mut on_map: std::collections::HashMap<String, Vec<String>> = std::collections::HashMap::new();
    for c in facts.all() {
        if let Claim::On(p, s) = c {
            on_map.entry(s.clone()).or_default().push(p.clone());
        }
    }
    for (a, b, c, d) in rects {
        let diag1 = Claim::seg_key(&a, &c);
        let diag2 = Claim::seg_key(&b, &d);
        let on1 = on_map.get(&diag1).cloned().unwrap_or_default();
        let on2 = on_map.get(&diag2).cloned().unwrap_or_default();
        // The diagonal intersection is the single-char point lying on both
        // diagonals (the shared interior point, not a shared vertex).
        let e = on1.iter().find(|p| p.chars().count() == 1 && on2.contains(p));
        if let Some(e) = e {
            facts.add(
                Claim::pred("IsMedian", &[e.clone(), diag1.clone()], Value::Bool(true)),
                Origin::Input,
            );
            facts.add(
                Claim::pred("IsMedian", &[e.clone(), diag2.clone()], Value::Bool(true)),
                Origin::Input,
            );
            facts.add(Claim::seg_eq(&diag1, &diag2), Origin::Input);
            let ea = Claim::seg_key(e, &a);
            let eb = Claim::seg_key(e, &b);
            let ec = Claim::seg_key(e, &c);
            let ed = Claim::seg_key(e, &d);
            facts.add(Claim::seg_eq(&ea, &eb), Origin::Input);
            facts.add(Claim::seg_eq(&ea, &ec), Origin::Input);
            facts.add(Claim::seg_eq(&ea, &ed), Origin::Input);
            facts.add(
                Claim::pred("OnSameCircle", &[a.clone(), b.clone(), c.clone(), d.clone()], Value::Bool(true)),
                Origin::Input,
            );
        }
    }
}

/// Derive that a perpendicular foot from a rectangle center to a side is the
/// midpoint of that side.  In an isosceles triangle (e.g. ZAB with AZ=BZ),
/// the altitude from the apex to the base bisects the base.
pub fn derive_perpendicular_foot_midpoints(facts: &mut FactStore) {
    use crate::claim::Value;
    // Collect all rectangles and their centers.
    let mut rects: Vec<(String, String, String, String, String)> = Vec::new();
    for c in facts.all() {
        if let Claim::PredVal { name, args, value } = c {
            if name.eq_ignore_ascii_case("rectangle")
                && args.len() == 4
                && value == Value::Bool(true)
            {
                let pts: Vec<String> = args.iter().map(|p| Claim::norm_ref(p)).collect();
                // Find the center (intersection of diagonals).
                let diag1 = Claim::seg_key(&pts[0], &pts[2]);
                let diag2 = Claim::seg_key(&pts[1], &pts[3]);
                for c2 in facts.all() {
                    if let Claim::On(p, s) = c2 {
                        if (s == diag1 || s == diag2)
                            && p.chars().count() == 1
                        {
                            // Check if this point is on BOTH diagonals.
                            let on_other = if s == diag1 { &diag2 } else { &diag1 };
                            if facts.contains(&Claim::On(p.clone(), on_other.clone())) {
                                rects.push((pts[0].clone(), pts[1].clone(), pts[2].clone(), pts[3].clone(), p.clone()));
                                break;
                            }
                        }
                    }
                }
            }
        }
    }
    for (a, b, c, d, center) in &rects {
        let sides = [
            Claim::seg_key(a, b),
            Claim::seg_key(b, c),
            Claim::seg_key(c, d),
            Claim::seg_key(d, a),
        ];
        for side in &sides {
            let side_n = Claim::norm_seg(side);
            for c2 in facts.all() {
                if let Claim::PredVal { name, args, value } = c2 {
                    if name.eq_ignore_ascii_case("isperpendicular")
                        && args.len() == 2
                        && value == Value::Bool(true)
                    {
                        let seg_n = Claim::norm_seg(&args[0]);
                        let base_n = Claim::norm_seg(&args[1]);
                        if base_n == side_n && seg_n.len() == 2 {
                            let chars: Vec<char> = seg_n.chars().collect();
                            let e_ch = center.chars().next().unwrap();
                            if (chars[0] == e_ch && chars[1] != e_ch)
                                || (chars[1] == e_ch && chars[0] != e_ch)
                            {
                                let foot = if chars[0] == e_ch { chars[1] } else { chars[0] };
                                let foot_s = foot.to_string();
                                let on_fact = Claim::On(foot_s.clone(), side_n.clone());
                                if facts.contains(&on_fact) {
                                    facts.add(
                                        Claim::pred("IsMedian", &[foot_s, side_n.clone()], Value::Bool(true)),
                                        Origin::Input,
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

/// Compute transitive closure of On facts for midpoint chains only.
/// If X is on segment YZ, and Z is the midpoint of YW, then X is on YW.
fn transitive_on_closure(facts: &mut FactStore) {
    let mut changed = true;
    while changed {
        changed = false;
        let current: Vec<_> = facts.all().into_iter().filter(|c| matches!(c, Claim::On(_, _))).collect();
        for c1 in &current {
            if let Claim::On(x, yz) = c1 {
                // Check if yz is a segment Y-Z where Z is a midpoint of YW
                if let Some((_y, z)) = split_seg(yz) {
                    // Check if Z is midpoint of Y-W for some W
                    for c2 in &current {
                        if let Claim::On(z2, yw) = c2 {
                            if *z2 == z {
                                // Check if Z is midpoint of YW
                                let median_fact = Claim::pred("IsMedian", &[z.clone(), yw.clone()], Value::Bool(true));
                                if facts.contains(&median_fact) {
                                    // X on YZ and Z is midpoint of YW => X on YW
                                    if facts.add(Claim::On(x.clone(), yw.clone()), Origin::Input) {
                                        changed = true;
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

/// Split a segment reference into its two endpoints.
/// Returns (Y, Z) for segments like "ab" or "a-b".
pub fn split_seg(seg: &str) -> Option<(String, String)> {
    let s = seg.to_lowercase();
    if s.contains('-') {
        let parts: Vec<&str> = s.split('-').collect();
        if parts.len() == 2 {
            return Some((parts[0].to_string(), parts[1].to_string()));
        }
    } else if s.len() == 2 {
        let chars: Vec<char> = s.chars().collect();
        return Some((chars[0].to_string(), chars[1].to_string()));
    } else {
        // Multi-char point names: letter+digits? pairs (e.g., "bq2" = "b" + "q2")
        let points: Vec<String> = {
            let mut result = Vec::new();
            let mut i = 0;
            let bytes: Vec<char> = s.chars().collect();
            while i < bytes.len() {
                if !bytes[i].is_ascii_alphabetic() {
                    i += 1;
                    continue;
                }
                let start = i;
                i += 1;
                while i < bytes.len() && bytes[i].is_ascii_digit() {
                    i += 1;
                }
                result.push(bytes[start..i].iter().collect());
            }
            result
        };
        if points.len() == 2 {
            return Some((points[0].clone(), points[1].clone()));
        }
    }
    None
}

/// Apply every proof block to `facts`, respecting `proofProperties`.
/// Claims established inside `Global`-scope proofs are added to `facts`, so
/// later goals and proofs may reuse them; `Local`-scope proofs are validated
/// against a throwaway store whose claims are discarded. Returns the
/// diagnostics produced while processing the proofs.
pub fn apply_proofs(file: &File, facts: &mut FactStore) -> Vec<Diagnostic> {
    let mut diags = Vec::new();

    let scope_map: HashMap<u32, Scope> = file
        .props
        .iter()
        .map(|p| (p.index, p.scope))
        .collect();

    for proof in &file.proofs {
        let scope = scope_map.get(&proof.index).copied().unwrap_or(Scope::Global);
        let mut local = FactStore::new();
        let store: &mut FactStore = if scope == Scope::Local { &mut local } else { facts };
        // Apply scoped inp[N]: statements for this proof's goal index.
        for (idx, stmt) in &file.scoped_input {
            if *idx == proof.index {
                process_input(stmt, store, &mut diags, &std::collections::HashMap::new(), &std::collections::HashMap::new());
            }
        }
        process_proof(proof, store, &mut diags);
    }

    diags
}

/// Collect the named perpendicular lines in the input section:
/// `L = PerpendicularLine(A, BC)` maps `l` -> `(a, bc)`. Used to resolve
/// `Intersection(L, ...)` references.
fn known_perp_lines(file: &File) -> std::collections::HashMap<String, (String, String)> {
    let mut m = std::collections::HashMap::new();
    for stmt in &file.input {
        if let InputStmt::Assign { name, geom, .. } = stmt {
            if let Geom::PerpendicularLine { point, base, .. } = geom {
                m.insert(
                    Claim::norm_ref(name),
                    (Claim::norm_ref(point), base.clone()),
                );
            }
        }
    }
    m
}

/// The canonical radius key of a declared circle: an internal segment name
/// whose length is the circle's radius.
pub fn circle_radius_key(circle: &str) -> String {
    format!("{}__radius", Claim::norm_ref(circle))
}

/// Collect declared circles: `K = Circle(O, ...)` maps `k` -> center.
fn known_circles(file: &File) -> std::collections::HashMap<String, String> {
    let mut m = std::collections::HashMap::new();
    for stmt in &file.input {
        if let InputStmt::Assign { name, geom, .. } = stmt {
            if let Geom::Circle { center, .. } = geom {
                m.insert(Claim::norm_ref(name), Claim::norm_ref(center));
            }
        }
    }
    m
}

/// Check a whole file, returning diagnostics.
pub fn check(file: &File) -> Vec<Diagnostic> {
    let mut facts = FactStore::new();
    let mut diags = Vec::new();
    let known = known_perp_lines(file);
    let circles = known_circles(file);

    for stmt in &file.input {
        process_input(stmt, &mut facts, &mut diags, &known, &circles);
    }

    derive_global_facts(&mut facts);

    diags.extend(apply_proofs(file, &mut facts));

    check_goals(file, &facts, &mut diags);

    diags
}

// ---- input processing ----

fn process_input(
    stmt: &InputStmt,
    facts: &mut FactStore,
    diags: &mut Vec<Diagnostic>,
    known: &std::collections::HashMap<String, (String, String)>,
    circles: &std::collections::HashMap<String, String>,
) {
    match stmt {
        InputStmt::Triangle { name, points, props, pos } => {
            let tri = Claim::norm_ref(name);
            // Record the triangle itself so cos() resolution can find it.
            facts.add(
                Claim::pred("Triangle", &[tri.clone()], Value::Bool(true)),
                Origin::Input,
            );
            // Degenerate triangle: two or more coincident vertices.
            {
                let mut seen: Vec<String> = Vec::new();
                for p in points {
                    let pn = Claim::norm_ref(p);
                    if seen.contains(&pn) {
                        diags.push(Diagnostic::error(
                            span_of(*pos, 10),
                            format!("degenerate triangle: repeated vertex `{}`", p),
                        ));
                        break;
                    }
                    seen.push(pn);
                }
            }
            validate_triangle_props(props, *pos, diags);
            for (pname, pval) in props {
                match pname.as_str() {
                    "isoscelesat" => {
                        if let Value::Point(apex) = pval {
                            facts.add(
                                Claim::pred("IsIsosceles", &[tri.clone()], Value::Bool(true)),
                                Origin::Input,
                            );
                            facts.add(
                                Claim::IsoscelesAt(tri.clone(), apex.clone()),
                                Origin::Input,
                            );
                        }
                    }
                    "acute" => {
                        if let Value::Bool(b) = pval {
                            if *b {
                                facts.add(
                                    Claim::pred("IsAcute", &[tri.clone()], Value::Bool(true)),
                                    Origin::Input,
                                );
                            }
                        }
                    }
                    "rightat" => {
                        if let Value::Point(p) = pval {
                            facts.add(
                                Claim::pred("IsRight", &[tri.clone()], Value::Bool(true)),
                                Origin::Input,
                            );
                            facts.add(
                                Claim::PredVal {
                                    name: "rightat".into(),
                                    args: vec![tri.clone()],
                                    value: Value::Point(p.clone()),
                                },
                                Origin::Input,
                            );
                        }
                    }
                    "obtuseat" => {
                        if let Value::Point(p) = pval {
                            facts.add(
                                Claim::pred("IsObtuse", &[tri.clone()], Value::Bool(true)),
                                Origin::Input,
                            );
                            facts.add(
                                Claim::PredVal {
                                    name: "obtuseat".into(),
                                    args: vec![tri.clone()],
                                    value: Value::Point(p.clone()),
                                },
                                Origin::Input,
                            );
                        }
                    }
                    _ => {}
                }
            }
            let _ = points;
            // Add On facts for triangle vertices on their sides
            if points.len() == 3 {
                let sides = [
                    (&points[0], &points[1]),
                    (&points[1], &points[2]),
                    (&points[2], &points[0]),
                ];
                for (a, b) in sides {
                    let seg = Claim::seg_key(a, b);
                    facts.add(Claim::On(Claim::norm_ref(a), seg.clone()), Origin::Input);
                    facts.add(Claim::On(Claim::norm_ref(b), seg), Origin::Input);
                }
            }
        }
        InputStmt::Assign { name, geom, pos } => {
            process_construction(name, geom, *pos, facts, diags, known, circles);
        }
        InputStmt::Segment { a, b, pos } => {
            let an = Claim::norm_ref(a);
            let bn = Claim::norm_ref(b);
            let seg = Claim::seg_key(&an, &bn);
            facts.add(Claim::On(an.clone(), seg.clone()), Origin::Input);
            facts.add(Claim::On(bn.clone(), seg.clone()), Origin::Input);
            facts.add(Claim::OnSegment(an, seg.clone()), Origin::Input);
            facts.add(Claim::OnSegment(bn, seg), Origin::Input);
            let _ = pos;
        }
        InputStmt::Line { a, b, pos } => {
            let an = Claim::norm_ref(a);
            let bn = Claim::norm_ref(b);
            let line = Claim::seg_key(&an, &bn);
            facts.add(Claim::On(an, line.clone()), Origin::Input);
            facts.add(Claim::On(bn, line.clone()), Origin::Input);
            let _ = pos;
        }
        InputStmt::EqChain { items, pos } => {
            for pair in items.windows(2) {
                let l = &pair[0];
                let r = &pair[1];
                if !l.is_num() && !r.is_num() && l.squared() != r.squared() {
                    diags.push(Diagnostic::error(
                        span_of(*pos, 12),
                        "cannot compare a squared length with a plain length",
                    ));
                    continue;
                }
                if let Some(n) = l.numeric().or(r.numeric()) {
                    // `AD=3` / `Distance(A,H)=7`: a numeric length fact.
                    let n_u32 = n.round() as u32;
                    let seg = if l.is_num() { r.seg() } else { l.seg() };
                    if l.squared() || r.squared() {
                        facts.add(Claim::sq_eq(&seg, n_u32), Origin::Input);
                    } else {
                        facts.add(Claim::len_eq(&seg, n_u32), Origin::Input);
                    }
                } else {
                    facts.add(
                        Claim::seg_eq(&l.seg(), &r.seg()),
                        Origin::Input,
                    );
                }
            }
            let _ = pos;
        }
        InputStmt::AngleEq { lhs, rhs, pos } => {
            facts.add(Claim::angle_eq(lhs, rhs), Origin::Input);
            let _ = pos;
        }
        InputStmt::PredFact { name, args, value, pos } => {
            facts.add(Claim::pred(name, args, value.clone()), Origin::Input);
            // Auto-create Triangle fact for rightat/obtuseat/isoscelesat predicates
            // so trig evaluation can find the triangle.
            if (name.eq_ignore_ascii_case("rightat")
                || name.eq_ignore_ascii_case("obtuseat")
                || name.eq_ignore_ascii_case("isoscelesat"))
                && args.len() == 1
                && args[0].len() == 3
            {
                let tri = Claim::norm_ref(&args[0]);
                if !facts.contains(&Claim::pred("triangle", &[tri.clone()], Value::Bool(true))) {
                    facts.add(
                        Claim::pred("triangle", &[tri], Value::Bool(true)),
                        Origin::Input,
                    );
                }
            }
            // `IsRectangle(A,B,C,D)=true` (vertices in order): derive the
            // side structure — opposite sides parallel, adjacent sides
            // perpendicular — so the rule base can reason about it.
            if name.eq_ignore_ascii_case("isrectangle")
                && args.len() == 4
                && *value == Value::Bool(true)
            {
                let pts: Vec<String> = args.iter().map(|p| Claim::norm_ref(p)).collect();
                let seg = |i: usize| -> String { Claim::seg_key(&pts[i], &pts[(i + 1) % 4]) };
                for i in 0..4 {
                    let a = seg(i);
                    let b = seg((i + 1) % 4);
                    facts.add(
                        Claim::pred(
                            "IsPerpendicular",
                            &[a.clone(), b],
                            Value::Bool(true),
                        ),
                        Origin::Input,
                    );
                }
                for i in 0..2 {
                    let a = seg(i);
                    let b = seg(i + 2);
                    facts.add(
                        Claim::pred("IsParallel", &[a.clone(), b], Value::Bool(true)),
                        Origin::Input,
                    );
                }
            }
            let _ = pos;
        }
        InputStmt::RatioEq { lhs, rhs, pos } => {
            facts.add(Claim::ratio_eq(lhs, rhs), Origin::Input);
            let _ = pos;
        }
    }
}

fn validate_triangle_props(
    props: &[(String, Value)],
    pos: crate::ast::Pos,
    diags: &mut Vec<Diagnostic>,
) {
    let mut rightat: Option<&Value> = None;
    let mut obtuseat: Option<&Value> = None;
    let mut acute: Option<bool> = None;

    for (pname, pval) in props {
        match pname.as_str() {
            "isoscelesat" => {
                if !matches!(pval, Value::Point(_) | Value::None_ | Value::Any) {
                    diags.push(Diagnostic::error(
                        span_of(pos, 10),
                        format!("property `{}` must be Any | Point | None", pname),
                    ));
                }
            }
            "acute" => {
                if let Value::Bool(b) = pval {
                    acute = Some(*b);
                } else {
                    diags.push(Diagnostic::error(
                        span_of(pos, 10),
                        "property `acute` must be a Bool",
                    ));
                }
            }
            "rightat" => {
                rightat = Some(pval);
            }
            "obtuseat" => {
                obtuseat = Some(pval);
            }
            _ => {}
        }
    }

    // TriangleProperties `throws on` rules.
    let right_set = matches!(rightat, Some(Value::Point(_)));
    let obtuse_set = matches!(obtuseat, Some(Value::Point(_)));
    if right_set && obtuse_set {
        diags.push(Diagnostic::error(
            span_of(pos, 10),
            "throws on (!IsNone(rightAt) && !IsNone(obtuseAt))",
        ));
    }
    if acute == Some(true) && (right_set || obtuse_set) {
        diags.push(Diagnostic::error(
            span_of(pos, 10),
            "throws on (acute && (!IsNone(rightAt) || !IsNone(obtuseAt)))",
        ));
    }
}

/// What a reference operand denotes: a segment, or a named perpendicular line.
enum RefId {
    Seg(String),
    Perp(String, String), // point, base
}

fn ref_identity(
    r: &str,
    known: &std::collections::HashMap<String, (String, String)>,
) -> Option<RefId> {
    if r.chars().count() == 2 {
        Some(RefId::Seg(Claim::norm_seg(r)))
    } else {
        known
            .get(&Claim::norm_ref(r))
            .map(|(p, b)| RefId::Perp(p.clone(), b.clone()))
    }
}

fn same_geom_line(
    a: &Geom,
    b: &Geom,
    known: &std::collections::HashMap<String, (String, String)>,
) -> bool {
    match (a, b) {
        (Geom::Ref(r1), Geom::Ref(r2)) => match (ref_identity(r1, known), ref_identity(r2, known)) {
            (Some(RefId::Seg(s1)), Some(RefId::Seg(s2))) => s1 == s2,
            (Some(RefId::Perp(p1, b1)), Some(RefId::Perp(p2, b2))) => {
                Claim::norm_ref(&p1) == Claim::norm_ref(&p2)
                    && Claim::norm_seg(&b1) == Claim::norm_seg(&b2)
            }
            _ => false,
        },
        (
            Geom::PerpendicularLine { point: p1, base: b1, .. },
            Geom::PerpendicularLine { point: p2, base: b2, .. },
        ) => Claim::norm_ref(p1) == Claim::norm_ref(p2)
            && Claim::norm_seg(b1) == Claim::norm_seg(b2),
        _ => false,
    }
}

/// True if a `IsParallel(line1, line2)=true` fact relates the two operands
/// (they have no intersection).
fn lines_parallel(a: &Geom, b: &Geom, facts: &FactStore) -> bool {
    let mut ls = Vec::new();
    for g in [a, b] {
        match g {
            Geom::Ref(r) if r.chars().count() == 2 => {
                ls.push(Claim::norm_seg(r));
            }
            _ => {}
        }
    }
    if ls.len() != 2 {
        return false;
    }
    facts.contains(&Claim::pred(
        "IsParallel",
        &[ls[0].clone(), ls[1].clone()],
        Value::Bool(true),
    )) || facts.contains(&Claim::pred(
        "IsParallel",
        &[ls[1].clone(), ls[0].clone()],
        Value::Bool(true),
    ))
}

fn process_construction(
    name: &str,
    geom: &Geom,
    pos: crate::ast::Pos,
    facts: &mut FactStore,
    diags: &mut Vec<Diagnostic>,
    known: &std::collections::HashMap<String, (String, String)>,
    circles: &std::collections::HashMap<String, String>,
) {
    let n = Claim::norm_ref(name);

    match geom {
        Geom::Intersection(geoms, ipos) => {
            // The operands must be segments or lines, and there must be more
            // than one of them.
            if geoms.len() < 2 {
                diags.push(Diagnostic::error(
                    span_of(*ipos, 12),
                    "Intersection requires more than 1 segment or line",
                ));
            }
            // `Intersection` throws on multiple intersections (coincident
            // lines) and on no intersection (parallel lines).
            for (i, a) in geoms.iter().enumerate() {
                for b in geoms.iter().skip(i + 1) {
                    if same_geom_line(a, b, known) {
                        diags.push(Diagnostic::error(
                            span_of(*ipos, 12),
                            "Intersection throws on multiple intersections",
                        ));
                    }
                    if lines_parallel(a, b, facts) {
                        diags.push(Diagnostic::error(
                            span_of(*ipos, 12),
                            "Intersection throws on no intersection (parallel lines)",
                        ));
                    }
                }
            }
            // The intersection point lies on every operand.
            for g in geoms {
                // Normalize the intersection point name to lowercase for
                // consistency with angle / ratio normalization.
                let n_norm = Claim::norm_ref(&n);
                match g {
                    Geom::Ref(r) => {
                        if r.chars().count() == 2 {
                            let seg_n = Claim::norm_seg(r);
                            facts.add(Claim::On(n_norm.clone(), seg_n.clone()), Origin::Input);
                            facts.add(Claim::OnSegment(n_norm.clone(), seg_n), Origin::Input);
                        } else if let Some((point, base)) = known.get(&Claim::norm_ref(r)) {
                            // A named perpendicular line `L = PerpendicularLine(point, base)`:
                            // the intersection point lies on the base, and the
                            // segment from `point` to it is perpendicular to the base.
                            let base_n = Claim::norm_seg(base);
                            facts.add(Claim::On(n_norm.clone(), base_n.clone()), Origin::Input);
                            facts.add(Claim::OnSegment(n_norm.clone(), base_n), Origin::Input);
                            let seg = Claim::seg_key(point, &n_norm);
                            facts.add(
                                Claim::pred(
                                    "IsPerpendicular",
                                    &[seg.clone(), base.clone()],
                                    Value::Bool(true),
                                ),
                                Origin::Input,
                            );
                            facts.add(
                                Claim::On(Claim::norm_ref(point), Claim::norm_seg(&seg)),
                                Origin::Input,
                            );
                        } else {
                            diags.push(Diagnostic::error(
                                span_of(*ipos, 12),
                                "Intersection(Segment|Line...) requires segment or line arguments",
                            ));
                        }
                    }
                    Geom::PerpendicularLine { point, base, .. } => {
                        // The point lies on the base, and the perpendicular
                        // through `point` to the base is perpendicular to it.
                        let base_n = Claim::norm_seg(base);
                        facts.add(Claim::On(n_norm.clone(), base_n.clone()), Origin::Input);
                        facts.add(Claim::OnSegment(n_norm.clone(), base_n), Origin::Input);
                        let seg = Claim::seg_key(point, &n_norm);
                        facts.add(
                            Claim::pred(
                                "IsPerpendicular",
                                &[seg.clone(), base.clone()],
                                Value::Bool(true),
                            ),
                            Origin::Input,
                        );
                        facts.add(
                            Claim::On(Claim::norm_ref(point), Claim::norm_seg(&seg)),
                            Origin::Input,
                        );
                        // Auto-derive right angles: the perpendicular segment
                        // creates right triangles at the foot.
                        let pchars: Vec<char> = point.chars().collect();
                        let hchars: Vec<char> = n_norm.chars().collect();
                        if pchars.len() == 1 && hchars.len() == 1 && base.len() == 2 {
                            let a = base.chars().next().unwrap();
                            let b = base.chars().nth(1).unwrap();
                            for x in [a, b] {
                                let tri = format!(
                                    "{}{}{}",
                                    pchars[0].to_lowercase(),
                                    hchars[0].to_lowercase(),
                                    x.to_lowercase()
                                );
                                facts.add(
                                    Claim::pred("IsRight", &[tri.clone()], Value::Bool(true)),
                                    Origin::Input,
                                );
                                facts.add(
                                    Claim::PredVal {
                                        name: "rightat".into(),
                                        args: vec![tri.clone()],
                                        value: Value::Point(n_norm.clone()),
                                    },
                                    Origin::Input,
                                );
                                facts.add(
                                    Claim::PredVal {
                                        name: "triangle".into(),
                                        args: vec![tri],
                                        value: Value::Bool(true),
                                    },
                                    Origin::Input,
                                );
                            }
                        }
                    }
                    Geom::Line { a, b, .. } => {
                        // An explicit line: the intersection point lies on it.
                        facts.add(
                            Claim::On(n_norm.clone(), Claim::seg_key(a, b)),
                            Origin::Input,
                        );
                        // The intersection point and the two line endpoints are
                        // collinear: a, b, Q2 are on the same line.
                        facts.add(
                            Claim::pred(
                                "iscollinear",
                                &[a.clone(), b.clone(), n_norm.to_string()],
                                Value::Bool(true),
                            ),
                            Origin::Input,
                        );
                    }
                    _ => {
                        diags.push(Diagnostic::error(
                            span_of(*ipos, 12),
                            "Intersection(Segment|Line...) requires segment or line arguments",
                        ));
                    }
                }
            }
        }
        Geom::PerpendicularLine { point, base, pos: ppos } => {
            // A named perpendicular line: `L = PerpendicularLine(A, BC)`.
            let seg = Claim::seg_key(point, &n);
            facts.add(
                Claim::pred("IsPerpendicular", &[seg.clone(), base.clone()], Value::Bool(true)),
                Origin::Input,
            );
            facts.add(
                Claim::On(Claim::norm_ref(point), Claim::norm_seg(&seg)),
                Origin::Input,
            );
            let _ = ppos;
        }
        Geom::Midpoint { a, b, pos: mpos } => {
            // `M = Midpoint(A, B)` establishes the median fact directly.
            let seg = Claim::seg_key(a, b);
            facts.add(
                Claim::pred("IsMedian", &[n.clone(), seg.clone()], Value::Bool(true)),
                Origin::Input,
            );
            let seg_n = Claim::norm_seg(&seg);
            facts.add(Claim::On(n.clone(), seg_n.clone()), Origin::Input);
            facts.add(Claim::OnSegment(n.clone(), seg_n), Origin::Input);
            facts.add(Claim::seg_eq(&Claim::seg_key(&n, a), &Claim::seg_key(&n, b)), Origin::Input);
            let _ = mpos;
        }
        Geom::AngleBisector { vertex, base, pos: bpos } => {
            // `D = AngleBisector(A, BC)`: the foot of the A-bisector on BC.
            // The bisected angle is `BAC` (vertex in the middle).
            let seg = Claim::seg_key(vertex, &n);
            let v = vertex.to_lowercase();
            let arms: Vec<char> = base.to_lowercase().chars().collect();
            let angle = if arms.len() == 2 {
                format!("{}{}{}", arms[0], v, arms[1])
            } else {
                format!("{}{}", v, base.to_lowercase())
            };
            facts.add(
                Claim::pred("IsAngleBisector", &[seg.clone(), angle], Value::Bool(true)),
                Origin::Input,
            );
            let base_n = Claim::norm_seg(base);
            facts.add(Claim::On(n.clone(), base_n.clone()), Origin::Input);
            facts.add(Claim::OnSegment(n.clone(), base_n), Origin::Input);
            let _ = bpos;
        }
        Geom::Altitude { vertex, base, pos: apos } => {
            // `H = Altitude(A, BC)` or `H = Altitude(A, ABC)`: the
            // perpendicular foot on the base (opposite side of the triangle).
            let base = if base.chars().count() == 3 {
                // A triangle reference: the base is the side opposite the
                // vertex, e.g. `Altitude(A, ABC)` -> foot on `BC`.
                let v = vertex.to_lowercase();
                let chars: Vec<char> = base.to_lowercase().chars().collect();
                let opp: String = chars.iter().filter(|&&c| c.to_string() != v).collect();
                opp
            } else {
                base.clone()
            };
            let seg = Claim::seg_key(vertex, &n);
            facts.add(
                Claim::pred("IsAltitude", &[seg.clone(), base.clone()], Value::Bool(true)),
                Origin::Input,
            );
            facts.add(
                Claim::pred("IsPerpendicular", &[seg.clone(), base.clone()], Value::Bool(true)),
                Origin::Input,
            );
            let base_n = Claim::norm_seg(&base);
            facts.add(Claim::On(n.clone(), base_n.clone()), Origin::Input);
            facts.add(Claim::OnSegment(n.clone(), base_n), Origin::Input);
            let _ = apos;
        }
        Geom::Center { kind, tri, pos: cpos } => {
            // Triangle centers: `O = Circumcenter(ABC)` etc.
            let pred = match kind {
                crate::ast::CenterKind::Circumcenter => "IsCircumcenter",
                crate::ast::CenterKind::Incenter => "IsIncenter",
                crate::ast::CenterKind::Orthocenter => "IsOrthocenter",
                crate::ast::CenterKind::Centroid => "IsCentroid",
            };
            facts.add(
                Claim::pred(pred, &[n.clone(), tri.clone()], Value::Bool(true)),
                Origin::Input,
            );
            let _ = cpos;
        }
        Geom::PointOn { seg, line_pts, pos: ppos } => {
            // `P = PointOn(K)` where K is a declared circle: P lies on K,
            // i.e. its distance from the center equals the radius.
            if line_pts.is_none() {
                if let Some(center) = circles.get(&Claim::norm_ref(seg)) {
                    let center = center.clone();
                    facts.add(
                        Claim::RadiusEq(
                            Claim::norm_ref(seg),
                            Claim::seg_key(&center, &n),
                        ),
                        Origin::Input,
                    );
                    facts.add(Claim::on_circle(&n, seg), Origin::Input);
                    let _ = ppos;
                    return;
                }
            }
            // `D = PointOn(AB)`: the point lies on the segment/line.
            let seg_n = Claim::norm_seg(seg);
            facts.add(Claim::On(n.clone(), seg_n.clone()), Origin::Input);
            facts.add(Claim::OnSegment(n.clone(), seg_n.clone()), Origin::Input);
            // `M = PointOn(Line(H,E))`: both endpoints lie on the line too.
            if let Some((a, b)) = line_pts {
                facts.add(Claim::On(Claim::norm_ref(a), seg_n.clone()), Origin::Input);
                facts.add(Claim::On(Claim::norm_ref(b), seg_n), Origin::Input);
            }
            let _ = ppos;
        }
        Geom::Line { a, b, pos: lpos } => {
            // `L = Line(A, B)`: both endpoints lie on the line.
            let seg = Claim::seg_key(a, b);
            facts.add(Claim::On(Claim::norm_ref(a), seg.clone()), Origin::Input);
            facts.add(Claim::On(Claim::norm_ref(b), seg), Origin::Input);
            let _ = lpos;
        }
        Geom::Ref(_) => {}
        Geom::ParallelLine { .. } => {}
        Geom::Circle { center, radius, .. } => {
            // `K = Circle(O[, r])`: establish the circle's radius as a
            // dedicated Radius(K)=… claim (readable, unscrambled), which
            // the length closures treat like any other equality.
            let c = Claim::norm_ref(center);
            facts.add(
                Claim::pred("IsCircleCenter", &[n.clone(), c.clone()], Value::Bool(true)),
                Origin::Input,
            );
            match radius {
                None => {}
                Some(RadiusSpec::Num(v)) => {
                    facts.add(Claim::RadiusEq(n.clone(), v.to_string()), Origin::Input);
                }
                Some(RadiusSpec::Seg(s)) => {
                    facts.add(
                        Claim::RadiusEq(n.clone(), Claim::norm_seg(s)),
                        Origin::Input,
                    );
                }
                Some(RadiusSpec::ThroughPoint(p)) => {
                    let p = Claim::norm_ref(p);
                    facts.add(
                        Claim::RadiusEq(n.clone(), Claim::seg_key(&c, &p)),
                        Origin::Input,
                    );
                    facts.add(Claim::on_circle(&p, &n), Origin::Input);
                }
            }
        }
    }
    let _ = pos;
}

// ---- proof processing ----

fn process_proof(
    proof: &crate::ast::ProofBlock,
    facts: &mut FactStore,
    diags: &mut Vec<Diagnostic>,
) {
    let mut skipped = false;
    let mut step_num = 0usize;

    for step in &proof.steps {
        step_num += 1;
        match step {
            Step::Nothing(_) => {
                skipped = true;
            }
            Step::Chain { claims, pos } => {
                if skipped {
                    diags.push(Diagnostic::warning(
                        span_of(*pos, expr_len(&claims[0])),
                        "Proofs after Nothing",
                    ));
                    check_duplicate_conclusion(claims, facts, proof.index, diags);
                    continue;
                }
                process_chain(claims, proof.index, step_num, facts, diags);
            }
        }
    }
}

fn check_duplicate_conclusion(
    claims: &[ClaimExpr],
    facts: &FactStore,
    proof_index: u32,
    diags: &mut Vec<Diagnostic>,
) {
    if let Some(last) = claims.last() {
        let atoms = claim_atoms(last);
        if !atoms.is_empty() && atoms.iter().all(|a| facts.contains(a)) {
            let origin = facts.get(&atoms[0]).map(|f| f.origin.clone());
            let note = match origin {
                Some(Origin::Proof(i, _)) => {
                    format!("It was already established at proof[{}]", i)
                }
                _ => "It was already established".to_string(),
            };
            diags.push(
                Diagnostic::warning(
                    span_of(last.pos(), expr_len(last)),
                    "Already established proof",
                )
                .with_note(note),
            );
            let _ = proof_index;
        }
    }
}

fn process_chain(
    claims: &[ClaimExpr],
    proof_index: u32,
    step_num: usize,
    facts: &mut FactStore,
    diags: &mut Vec<Diagnostic>,
) {
    // Check for unknown predicate names and suggest corrections.
    fn check_pred_names(claims: &[ClaimExpr], diags: &mut Vec<Diagnostic>) {
        for claim in claims {
            let (name, pos) = match claim {
                ClaimExpr::PredEq { name, pos, .. } => (name.as_str(), *pos),
                ClaimExpr::PredCall { name, pos, .. } => (name.as_str(), *pos),
                ClaimExpr::Conj { items, .. } => {
                    check_pred_names(items, diags);
                    continue;
                }
                _ => continue,
            };
            let low = name.to_lowercase();
            if let Some(suggestion) = suggest_predicate(&low) {
                diags.push(
                    Diagnostic::error(
                        span_of(pos, name.len()),
                        format!("unknown predicate `{}`", crate::claim::display_predicate(name)),
                    )
                    .with_note(format!("did you mean `{}`?", suggestion)),
                );
            }
        }
    }
    check_pred_names(claims, diags);
    if claims.len() == 1 {
        let expr = &claims[0];
        let atoms = claim_atoms(expr);
        if atoms.is_empty() {
            // Sum claims have no atoms — verify numerically.
            if let ClaimExpr::Sum { lhs, rhs, .. } = expr {
                if crate::symbolic::sum_solves(lhs, rhs, facts)
                    || crate::symbolic::sum_solves_trig(lhs, rhs, facts)
                {
                    return;
                }
                diags.push(Diagnostic::error(
                    span_of(expr.pos(), expr_len(expr)),
                    "Sum identity could not be verified",
                ));
                return;
            }
            // EqChain with arithmetic expressions — verify each pair numerically.
            if let ClaimExpr::EqChain { items, .. } = expr {
                let mut ok = true;
                for pair in items.windows(2) {
                    let lv = crate::symbolic::eval_len_expr(&pair[0], facts);
                    let rv = crate::symbolic::eval_len_expr(&pair[1], facts);
                    match (lv, rv) {
                        (Some(a), Some(b)) if (a - b).abs() < 1e-9 => { continue; }
                        _ => {}
                    }
                    ok = false;
                    break;
                }
                if ok {
                    return;
                }
            }
            diags.push(Diagnostic::error(
                span_of(expr.pos(), expr_len(expr)),
                "a proof step must conclude at least one claim",
            ));
            return;
        }
        for (i, atom) in atoms.iter().enumerate() {
            let extra: Vec<Claim> = atoms[..i].to_vec();
            establish(atom, &extra, facts, diags, expr.pos(), expr_len(expr), proof_index, step_num);
        }
        return;
    }

    // Premise of the chain must be established.
    let premise_atoms = claim_atoms(&claims[0]);
    for p in &premise_atoms {
        // Reflexive equalities (e.g. SegEq("bc","bc")) are trivially true.
        let is_reflexive = match p {
            Claim::SegEq(a, b) | Claim::TriEq(a, b) | Claim::AngleEq(a, b) => a == b,
            _ => false,
        };
        if is_reflexive {
            continue;
        }
        // SegEq(a,b) is established if a and b have the same length.
        let equal_len = if let Claim::SegEq(a, b) = p {
            let la = crate::symbolic::solve_len(a, facts);
            let lb = crate::symbolic::solve_len(b, facts);
            la.is_some() && lb.is_some() && la == lb
        } else {
            false
        };
        if facts.contains(p) || equal_len {
            continue;
        }
        // Ratio equalities can be verified numerically from segment lengths.
        if let Claim::RatioEq(_, _) = p {
            if crate::symbolic::ratio_solves(p, facts) {
                continue;
            }
        }
        diags.push(
            Diagnostic::error(
                span_of(claims[0].pos(), expr_len(&claims[0])),
                format!("Premise not established: {}", p),
            )
            .with_kind("premise-not-established"),
        );
    }

    for i in 0..claims.len() - 1 {
        let ante = claim_atoms(&claims[i]);
        let concl = &claims[i + 1];
        if let ClaimExpr::EqChain { items, .. } = concl {
            if eq_chain_mixed(items) {
                diags.push(Diagnostic::error(
                    span_of(concl.pos(), expr_len(concl)),
                    "proof step cannot compare a squared length with a plain length",
                ));
                continue;
            }
        }
        let concl_atoms = claim_atoms(concl);
        if concl_atoms.is_empty() {
            // Sum claims in chain conclusions — verify numerically.
            if let ClaimExpr::Sum { lhs, rhs, .. } = concl {
                if crate::symbolic::sum_solves(lhs, rhs, facts)
                    || crate::symbolic::sum_solves_trig(lhs, rhs, facts)
                {
                    continue;
                }
                diags.push(Diagnostic::error(
                    span_of(concl.pos(), expr_len(concl)),
                    "Sum identity could not be verified",
                ));
                continue;
            }
            // EqChain with arithmetic expressions — verify each pair numerically
            // or via ratio algebra.
            if let ClaimExpr::EqChain { items, .. } = concl {
                let mut ok = true;
                for pair in items.windows(2) {
                    let lv = crate::symbolic::eval_len_expr(&pair[0], facts);
                    let rv = crate::symbolic::eval_len_expr(&pair[1], facts);
                    match (lv, rv) {
                        (Some(a), Some(b)) if (a - b).abs() < 1e-9 => { continue; }
                        _ => {}
                    }
                    // Try ratio-based: Seg(a) = Add(Seg(b), Seg(b)) means a = 2*b,
                    // which follows from b/a = 1/2.
                    if let (LenExpr::Seg(a), LenExpr::Add(l, r)) = (&pair[0], &pair[1]) {
                        if l == r {
                            let ratio_goal = Claim::ratio_eq(
                                &RatioExpr::Quot {
                                    num: RatioAtom::Seg(l.seg()),
                                    den: RatioAtom::Seg(a.clone()),
                                },
                                &RatioExpr::Quot {
                                    num: RatioAtom::Int(1),
                                    den: RatioAtom::Int(2),
                                },
                            );
                            if facts.contains(&ratio_goal)
                                || crate::symbolic::ratio_solves(&ratio_goal, facts)
                            {
                                continue;
                            }
                        }
                    }
                    if let (LenExpr::Add(l, r), LenExpr::Seg(a)) = (&pair[0], &pair[1]) {
                        if l == r {
                            let ratio_goal = Claim::ratio_eq(
                                &RatioExpr::Quot {
                                    num: RatioAtom::Int(2),
                                    den: RatioAtom::Int(1),
                                },
                                &RatioExpr::Quot {
                                    num: RatioAtom::Seg(a.clone()),
                                    den: RatioAtom::Seg(l.seg()),
                                },
                            );
                            if facts.contains(&ratio_goal)
                                || crate::symbolic::ratio_solves(&ratio_goal, facts)
                            {
                                continue;
                            }
                        }
                    }
                    ok = false;
                    break;
                }
                if ok {
                    continue;
                }
            }
            diags.push(Diagnostic::error(
                span_of(concl.pos(), expr_len(concl)),
                "a conclusion must contain at least one claim",
            ));
            continue;
        }
        for atom in &concl_atoms {
            establish(atom, &ante, facts, diags, concl.pos(), expr_len(concl), proof_index, step_num);
        }
    }
}

/// Establish `goal` (either by a rule application or, failing that, by
/// recording the claim and reporting an error, as the spec requires).
fn establish(
    goal: &Claim,
    extra: &[Claim],
    facts: &mut FactStore,
    diags: &mut Vec<Diagnostic>,
    pos: crate::ast::Pos,
    len: usize,
    proof_index: u32,
    step_num: usize,
) {
    // Reflexive equalities are trivially true (e.g., TriEq("abc","abc")).
    match goal {
        Claim::TriEq(a, b) if a == b => {
            facts.add(goal.clone(), Origin::Proof(proof_index, step_num));
            return;
        }
        Claim::SegEq(a, b) if a == b => {
            facts.add(goal.clone(), Origin::Proof(proof_index, step_num));
            return;
        }
        // SegEq(a,b) is established if a and b have the same numeric length.
        Claim::SegEq(a, b) => {
            let la = crate::symbolic::solve_len(a, facts);
            let lb = crate::symbolic::solve_len(b, facts);
            if la.is_some() && lb.is_some() && la == lb {
                facts.add(goal.clone(), Origin::Proof(proof_index, step_num));
                return;
            }
        }
        _ => {}
    }

    if facts.contains(goal) {
        let note = match facts.get(goal).map(|f| f.origin.clone()) {
            Some(Origin::Proof(i, _)) => {
                format!("It was already established at proof[{}]", i)
            }
            _ => "It was already established".to_string(),
        };
        diags.push(
            Diagnostic::warning(
                span_of(pos, len),
                "Already established proof",
            )
            .with_note(note),
        );
        return;
    }

    let facts_all = facts.all();
    let mut applied = false;
    for rule in rule_base() {
        if !apply_rule(&rule, &facts_all, extra, goal).is_empty() {
            applied = true;
            break;
        }
    }

    // Numeric derivations (lengths, ratios, Pythagoras) also count as rules.
    if !applied && crate::symbolic::numeric_solves(goal, facts) {
        applied = true;
    }
    // Ratio equalities verified numerically from segment lengths.
    if !applied {
        if let Claim::RatioEq(..) = goal {
            if crate::symbolic::ratio_solves(goal, facts) {
                applied = true;
            }
        }
    }

    if applied {
        facts.add(goal.clone(), Origin::Proof(proof_index, step_num));
        return;
    }

    // Wrong result: no rule derives the claimed conclusion.
    let ante_str = render_conjunction(extra);
    let msg = if ante_str.is_empty() {
        format!("Wrong result: {}", goal)
    } else {
        format!("Wrong result: {} -> {}", ante_str, goal)
    };
    diags.push(
        Diagnostic::error(
            span_of(pos, len),
            msg,
        )
        .with_kind("wrong-result")
        .with_hint(hint_message(goal, &facts_all, extra)),
    );

    // The claim is still recorded so later proofs see it (as the spec shows
    // with "Already established proof ... at proof[1]").
    facts.add(goal.clone(), Origin::Proof(proof_index, step_num));
}

fn render_conjunction(claims: &[Claim]) -> String {
    if claims.is_empty() {
        return String::new();
    }
    if claims.len() == 1 {
        return claims[0].to_string();
    }
    let parts: Vec<String> = claims.iter().map(|c| c.to_string()).collect();
    format!("({})", parts.join(" && "))
}

fn hint_message(goal: &Claim, facts: &[Claim], extra: &[Claim]) -> String {
    match find_hint(facts, extra, goal, &rule_base()) {
        Some(expected) => {
            format!("modify {} to {}", goal.render_hint(goal), expected.render_hint(goal))
        }
        None => format!("no rule derives {}", goal),
    }
}

// ---- goals ----

fn check_goals(file: &File, facts: &FactStore, diags: &mut Vec<Diagnostic>) {
    let known = known_perp_lines(file);
    let circles = known_circles(file);
    for goal in &file.goals {
        // Build per-goal fact store: base facts + all scoped inputs up to this goal.
        let mut goal_facts = FactStore::new();
        for f in facts.all() {
            goal_facts.add(f, Origin::Input);
        }
        for (idx, stmt) in &file.scoped_input {
            if *idx <= goal.index {
                process_input(stmt, &mut goal_facts, diags, &known, &circles);
            }
        }
        let facts = &goal_facts;
        if let Some(claim) = &goal.claim {
            if let ClaimExpr::EqChain { items, .. } = claim {
                if eq_chain_mixed(items) {
                    diags.push(Diagnostic::error(
                        span_of(claim.pos(), expr_len(claim)),
                        "Goal cannot compare a squared length with a plain length",
                    ));
                    continue;
                }
                // Evaluate compound EqChain items numerically.
                if items.len() >= 2 {
                    // Try exact rational comparison first.
                    let rat_vals: Vec<Option<crate::symbolic::EXRat>> = items
                        .iter()
                        .map(|e| crate::symbolic::eval_len_expr_ratio(e, facts))
                        .collect();
                    if rat_vals.iter().all(|v| v.is_some())
                        && rat_vals[1..].iter().all(|v| *v.as_ref().unwrap() == *rat_vals[0].as_ref().unwrap())
                    {
                        continue;
                    }
                    // Fall back to f64 comparison for trig/irrationals.
                    let vals: Vec<Option<f64>> = items
                        .iter()
                        .map(|e| crate::symbolic::eval_len_expr(e, facts))
                        .collect();
                    if vals.iter().all(|v| v.is_some()) {
                        let v0 = vals[0].unwrap();
                        if vals[1..].iter().all(|v| (v.unwrap() - v0).abs() < 1e-9) {
                            continue;
                        }
                    }
                    // Algebraic law-of-cosines verification.
                    if crate::symbolic::law_of_cosines_solves(items, facts) {
                        continue;
                    }
                }
            }
            if let ClaimExpr::Sum { lhs, rhs, .. } = claim {
                if crate::symbolic::sum_solves(lhs, rhs, facts)
                    || crate::symbolic::sum_solves_trig(lhs, rhs, facts)
                {
                    continue;
                }
            }
            let atoms = claim_atoms(claim);
            let mut missing = Vec::new();
            for a in &atoms {
                if facts.contains(a) || crate::symbolic::numeric_solves(a, facts) {
                    continue;
                }
                // For predicate goals, try all rules for direct derivation.
                if matches!(a, Claim::PredVal { .. }) {
                    let facts_all = facts.all();
                    let mut found = false;
                    for rule in rule_base() {
                        if !apply_rule(&rule, &facts_all, &[], a).is_empty() {
                            found = true;
                            break;
                        }
                    }
                    if found {
                        continue;
                    }
                    // Forward chaining: iteratively derive new facts,
                    // up to 3 rounds, to bridge multi-step chains.
                    {
                        let mut chain = facts_all;
                        for _ in 0..3 {
                            let new = derive_all(&chain, &[]);
                            let mut added = false;
                            for f in new {
                                if !chain.contains(&f) {
                                    chain.push(f);
                                    added = true;
                                }
                            }
                            if !added || chain.contains(a) {
                                break;
                            }
                        }
                        if chain.contains(a) {
                            continue;
                        }
                    }
                }
                // For SegEq/RatioEq goals, try forward chaining to derive
                // intermediate RatioEq facts, then re-check numeric_solves.
                if matches!(a, Claim::SegEq(..) | Claim::RatioEq(..)) {
                    let rules = rule_base();
                    let saturated = crate::prover::forward_saturate(facts, &rules);
                    if crate::symbolic::numeric_solves(a, &saturated) {
                        continue;
                    }
                }
                missing.push(a);
            }
            if !missing.is_empty() {
                diags.push(
                    Diagnostic::error(
                        span_of(claim.pos(), expr_len(claim)),
                        format!("Goal {} not proven: {}", goal.index, render_expr(claim)),
                    )
                    .with_kind("goal-not-proven"),
                );
            }
        }
    }
}

pub fn render_len_expr(e: &LenExpr) -> String {
    match e {
        LenExpr::Seg(r) => r.to_uppercase(),
        LenExpr::Distance(a, b) => {
            format!("Distance({},{})", a.to_uppercase(), b.to_uppercase())
        }
        LenExpr::Num(n) => n.to_string(),
        LenExpr::Sq(inner) => format!("{}^{}", render_len_expr(inner), 2),
        LenExpr::Sqrt(inner) => format!("sqrt({})", render_len_expr(inner)),
        LenExpr::Add(l, r) => format!("{}+{}", render_len_expr(l), render_len_expr(r)),
        LenExpr::Sub(l, r) => format!("{}-{}", render_len_expr(l), render_len_expr(r)),
        LenExpr::Mul(l, r) => format!("{}*{}", render_len_expr(l), render_len_expr(r)),
        LenExpr::Div(l, r) => format!("{} / {}", render_len_expr(l), render_len_expr(r)),
        LenExpr::Trig(func, angle) => format!("{}({})", func, angle.to_uppercase()),
    }
}

fn render_ratio_atom(a: &RatioAtom) -> String {
    match a {
        RatioAtom::Seg(s) => s.to_uppercase(),
        RatioAtom::Int(n) => n.to_string(),
    }
}

fn render_ratio_expr(e: &RatioExpr) -> String {
    match e {
        RatioExpr::Seg(s) => s.to_uppercase(),
        RatioExpr::Quot { num, den } => {
            format!("{}/{}", render_ratio_atom(num), render_ratio_atom(den))
        }
    }
}

/// Render a claim expression the way the user wrote it (for diagnostics).
pub fn render_expr(expr: &ClaimExpr) -> String {
    use crate::claim::display_predicate;
    match expr {
        ClaimExpr::EqChain { items, .. } => {
            let parts: Vec<String> = items.iter().map(render_len_expr).collect();
            parts.join("=")
        }
        ClaimExpr::Sum { lhs, rhs, .. } => {
            fn term(t: &crate::ast::SumTerm) -> String {
                use std::fmt::Write;
                let mut s = String::new();
                if let Some(l) = &t.len {
                    let _ = write!(s, "{}", render_len_expr(l));
                }
                if let Some(a) = &t.cos_angle {
                    if !s.is_empty() {
                        s.push('*');
                    }
                    let _ = write!(s, "cos({})", a.to_uppercase());
                }
                if t.neg {
                    s.insert(0, '-');
                }
                s
            }
            let l: Vec<String> = lhs.iter().map(term).collect();
            let r: Vec<String> = rhs.iter().map(term).collect();
            format!("{}={}", l.join("+"), r.join("+"))
        }
        ClaimExpr::PredEq { name, args, value, .. } => {
            let a: Vec<String> = args.iter().map(|s| s.to_uppercase()).collect();
            let base = format!("{}({})", display_predicate(name), a.join(","));
            match value {
                Value::Bool(true) => base,
                _ => format!("{}={}", base, value.render()),
            }
        }
        ClaimExpr::PredCall { name, args, .. } => {
            let a: Vec<String> = args.iter().map(|s| s.to_uppercase()).collect();
            format!("{}({})", display_predicate(name), a.join(","))
        }
        ClaimExpr::Conj { items, .. } => {
            let parts: Vec<String> = items.iter().map(render_expr).collect();
            format!("({})", parts.join(" && "))
        }
        ClaimExpr::TriEq { lhs, rhs, .. } => {
            format!("{}={}", lhs.to_uppercase(), rhs.to_uppercase())
        }
        ClaimExpr::TriCall { lhs, rhs, .. } => {
            format!(
                "Triangle({})=Triangle({})",
                lhs.to_uppercase(),
                rhs.to_uppercase()
            )
        }
        ClaimExpr::AngleEq { lhs, rhs, .. } => {
            format!(
                "Angle({})=Angle({})",
                lhs.to_uppercase(),
                rhs.to_uppercase()
            )
        }
        ClaimExpr::RatioEq { lhs, rhs, .. } => {
            format!("{}={}", render_ratio_expr(lhs), render_ratio_expr(rhs))
        }
    }
}

/// Per-atom display strings for a claim expression, using the user's
/// `Distance(...)` syntax when present. Used by the prover to render each
/// atom of a (possibly chained) goal exactly as written.
pub fn atom_display_strings(expr: &ClaimExpr) -> Vec<String> {
    match expr {
        ClaimExpr::EqChain { items, .. } => items
            .windows(2)
            .map(|pair| {
                format!(
                    "{}={}",
                    render_len_expr(&pair[0]),
                    render_len_expr(&pair[1])
                )
            })
            .collect(),
        _ => vec![render_expr(expr)],
    }
}




