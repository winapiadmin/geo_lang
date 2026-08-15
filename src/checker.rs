//! Proof checker: builds the fact store from the input section and validates
//! every proof block, producing diagnostics in the style of the language spec.

use crate::ast::{ClaimExpr, File, Geom, InputStmt, LenExpr, Scope, Step};
use crate::claim::{Claim, RatioAtom, RatioExpr, Value};
use crate::diag::{Diagnostic, Span};
use crate::rules::{apply_rule, find_hint, rule_base};
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
#[derive(Debug, Default)]
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
                    // `<number> = <len>`: the numeric side is on the left.
                    if r.squared() {
                        out.push(Claim::sq_eq(&r.seg(), n));
                    } else {
                        out.push(Claim::len_eq(&r.seg(), n));
                    }
                } else if let Some(n) = r.numeric() {
                    // `<len> = <number>`: a numeric length fact.
                    if l.squared() {
                        out.push(Claim::sq_eq(&l.seg(), n));
                    } else {
                        out.push(Claim::len_eq(&l.seg(), n));
                    }
                } else if l.squared() && r.squared() {
                    // `X^2 = Y^2`: equal squared lengths imply equal lengths
                    // (distances are nonnegative).
                    out.push(Claim::seg_eq(&l.seg(), &r.seg()));
                } else {
                    out.push(Claim::seg_eq(&l.seg(), &r.seg()));
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
    }
}

/// True if an equality chain compares a squared length with a plain one,
/// e.g. `BD^2 = CE`, which is a unit mismatch.
fn eq_chain_mixed(items: &[LenExpr]) -> bool {
    items.windows(2).any(|w| {
        let (l, r) = (&w[0], &w[1]);
        !l.is_num() && !r.is_num() && l.squared() != r.squared()
    })
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
    }
}

/// Convert an expression into the diagnostic underline length.
fn expr_len(expr: &ClaimExpr) -> usize {
    match expr {
        ClaimExpr::EqChain { items, .. } => {
            items.iter().map(len_expr_len).sum::<usize>() + (items.len() - 1)
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

/// Build the fact store from only the input section (used by the prover).
pub fn build_facts_from_input(file: &File) -> FactStore {
    let mut facts = FactStore::new();
    let mut diags = Vec::new();
    let known = known_perp_lines(file);
    for stmt in &file.input {
        process_input(stmt, &mut facts, &mut diags, &known);
    }
    facts
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

/// Check a whole file, returning diagnostics.
pub fn check(file: &File) -> Vec<Diagnostic> {
    let mut facts = FactStore::new();
    let mut diags = Vec::new();
    let known = known_perp_lines(file);

    for stmt in &file.input {
        process_input(stmt, &mut facts, &mut diags, &known);
    }

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
) {
    match stmt {
        InputStmt::Triangle { name, points, props, pos } => {
            let tri = Claim::norm_ref(name);
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
        }
        InputStmt::Assign { name, geom, pos } => {
            process_construction(name, geom, *pos, facts, diags, known);
        }
        InputStmt::Segment { a, b, pos } => {
            let seg = Claim::norm_seg(&format!("{}{}", a, b));
            let an = Claim::norm_ref(a);
            let bn = Claim::norm_ref(b);
            facts.add(Claim::On(an, seg.clone()), Origin::Input);
            facts.add(Claim::On(bn, seg.clone()), Origin::Input);
            let _ = pos;
        }
        InputStmt::Line { a, b, pos } => {
            let line = Claim::norm_seg(&format!("{}{}", a, b));
            let an = Claim::norm_ref(a);
            let bn = Claim::norm_ref(b);
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
                    let seg = if l.is_num() { r.seg() } else { l.seg() };
                    if l.squared() || r.squared() {
                        facts.add(Claim::sq_eq(&seg, n), Origin::Input);
                    } else {
                        facts.add(Claim::len_eq(&seg, n), Origin::Input);
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
                match g {
                    Geom::Ref(r) => {
                        if r.chars().count() == 2 {
                            facts.add(Claim::On(n.clone(), Claim::norm_seg(r)), Origin::Input);
                        } else if let Some((point, base)) = known.get(&Claim::norm_ref(r)) {
                            // A named perpendicular line `L = PerpendicularLine(point, base)`:
                            // the intersection point lies on the base, and the
                            // segment from `point` to it is perpendicular to the base.
                            facts.add(Claim::On(n.clone(), Claim::norm_seg(base)), Origin::Input);
                            let seg = format!("{}{}", point, n);
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
                        facts.add(Claim::On(n.clone(), Claim::norm_seg(base)), Origin::Input);
                        let seg = format!("{}{}", point, n);
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
                    }
                    Geom::Line { a, b, .. } => {
                        // An explicit line: the intersection point lies on it.
                        facts.add(
                            Claim::On(n.clone(), Claim::norm_seg(&format!("{}{}", a, b))),
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
            let seg = format!("{}{}", point, n);
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
            let seg = format!("{}{}", a, b);
            facts.add(
                Claim::pred("IsMedian", &[n.clone(), seg.clone()], Value::Bool(true)),
                Origin::Input,
            );
            facts.add(Claim::On(n.clone(), Claim::norm_seg(&seg)), Origin::Input);
            facts.add(Claim::seg_eq(&format!("{}{}", n, a), &format!("{}{}", n, b)), Origin::Input);
            let _ = mpos;
        }
        Geom::AngleBisector { vertex, base, pos: bpos } => {
            // `D = AngleBisector(A, BC)`: the foot of the A-bisector on BC.
            // The bisected angle is `BAC` (vertex in the middle).
            let seg = format!("{}{}", vertex, n);
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
            facts.add(Claim::On(n.clone(), Claim::norm_seg(base)), Origin::Input);
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
            let seg = format!("{}{}", vertex, n);
            facts.add(
                Claim::pred("IsAltitude", &[seg.clone(), base.clone()], Value::Bool(true)),
                Origin::Input,
            );
            facts.add(
                Claim::pred("IsPerpendicular", &[seg.clone(), base.clone()], Value::Bool(true)),
                Origin::Input,
            );
            facts.add(Claim::On(n.clone(), Claim::norm_seg(&base)), Origin::Input);
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
            // `D = PointOn(AB)`: the point lies on the segment/line.
            let seg_n = Claim::norm_seg(seg);
            facts.add(Claim::On(n.clone(), seg_n.clone()), Origin::Input);
            // `M = PointOn(Line(H,E))`: both endpoints lie on the line too.
            if let Some((a, b)) = line_pts {
                facts.add(Claim::On(Claim::norm_ref(a), seg_n.clone()), Origin::Input);
                facts.add(Claim::On(Claim::norm_ref(b), seg_n), Origin::Input);
            }
            let _ = ppos;
        }
        Geom::Line { a, b, pos: lpos } => {
            // `L = Line(A, B)`: both endpoints lie on the line.
            let seg = Claim::norm_seg(&format!("{}{}", a, b));
            facts.add(Claim::On(Claim::norm_ref(a), seg.clone()), Origin::Input);
            facts.add(Claim::On(Claim::norm_ref(b), seg), Origin::Input);
            let _ = lpos;
        }
        Geom::Ref(_) => {}
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
    if claims.len() == 1 {
        let expr = &claims[0];
        let atoms = claim_atoms(expr);
        if atoms.is_empty() {
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
        if !facts.contains(p) {
            diags.push(
                Diagnostic::error(
                    span_of(claims[0].pos(), expr_len(&claims[0])),
                    format!("Premise not established: {}", p),
                )
                .with_kind("premise-not-established"),
            );
        }
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

    if applied {
        facts.add(goal.clone(), Origin::Proof(proof_index, step_num));
        return;
    }

    // Wrong result: no rule derives the claimed conclusion.
    let ante_str = render_conjunction(extra);
    diags.push(
        Diagnostic::error(
            span_of(pos, len),
            format!("Wrong result: {} -> {}", ante_str, goal),
        )
        .with_kind("wrong-result")
        .with_hint(hint_message(goal, &facts_all, extra)),
    );

    // The claim is still recorded so later proofs see it (as the spec shows
    // with "Already established proof ... at proof[1]").
    facts.add(goal.clone(), Origin::Proof(proof_index, step_num));
}

fn render_conjunction(claims: &[Claim]) -> String {
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
    for goal in &file.goals {
        if let Some(claim) = &goal.claim {
            if let ClaimExpr::EqChain { items, .. } = claim {
                if eq_chain_mixed(items) {
                    diags.push(Diagnostic::error(
                        span_of(claim.pos(), expr_len(claim)),
                        "Goal cannot compare a squared length with a plain length",
                    ));
                    continue;
                }
            }
            let atoms = claim_atoms(claim);
            let mut missing = Vec::new();
            for a in &atoms {
                if !facts.contains(a) && !crate::symbolic::numeric_solves(a, facts) {
                    missing.push(a);
                }
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

fn render_len_expr(e: &LenExpr) -> String {
    match e {
        LenExpr::Seg(r) => r.to_uppercase(),
        LenExpr::Distance(a, b) => {
            format!("Distance({},{})", a.to_uppercase(), b.to_uppercase())
        }
        LenExpr::Num(n) => n.to_string(),
        LenExpr::Sq(inner) => format!("{}^{}", render_len_expr(inner), 2),
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