//! Core value and claim model for the .geo language.
//!
//! The language deals with atomic *claims*: predicate calls such as
//! `IsMedian(D, BC) = true`, segment equalities such as `BD = DC`, and
//! incidence facts. A `Claim` is a fully-normalized atomic fact used by the
//! fact store, rule engine, checker and prover.

use std::fmt;

/// A value that a predicate or property may take.
///
/// `Optional[T] = T | ?`, so a predicate may hold a concrete value or be
/// *unknown* (`?`). Comparing an unknown value throws.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Value {
    Bool(bool),
    /// A point reference such as `A`.
    Point(String),
    /// `None` / `null`.
    None_,
    /// The unconstrained `Any` value.
    Any,
    /// The unknown optional value `?`.
    Unknown,
}

impl Value {
    pub fn render(&self) -> String {
        match self {
            Value::Bool(b) => b.to_string(),
            Value::Point(p) => p.to_uppercase(),
            Value::None_ => "None".into(),
            Value::Any => "Any".into(),
            Value::Unknown => "?".into(),
        }
    }
}

/// An atom inside a ratio: a segment reference or an integer constant.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum RatioAtom {
    Seg(String),
    Int(u32),
}

/// A ratio expression: a bare segment length or a quotient of two atoms,
/// e.g. `BD`, `AB/AC`, `1/2`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum RatioExpr {
    Seg(String),
    Quot { num: RatioAtom, den: RatioAtom },
}

/// A stable ordering key for a ratio atom (used for canonicalization).
fn atom_key(a: &RatioAtom) -> String {
    match a {
        RatioAtom::Int(n) => format!("0{:08}", n),
        RatioAtom::Seg(s) => format!("1{}", s),
    }
}

/// A stable ordering key for a ratio expression.
fn ratio_key(e: &RatioExpr) -> String {
    match e {
        RatioExpr::Seg(s) => format!("0{}", s),
        RatioExpr::Quot { num, den } => format!("1{}/{}", atom_key(num), atom_key(den)),
    }
}

fn canon_atom(a: &RatioAtom) -> RatioAtom {
    match a {
        RatioAtom::Seg(s) => RatioAtom::Seg(Claim::norm_seg(s)),
        RatioAtom::Int(_) => a.clone(),
    }
}

/// Canonicalize a ratio expression: normalize segments and invert the
/// quotient if the denominator sorts before the numerator.
fn canon_ratio(e: &RatioExpr) -> RatioExpr {
    match e {
        RatioExpr::Seg(s) => RatioExpr::Seg(Claim::norm_seg(s)),
        RatioExpr::Quot { num, den } => {
            let n = canon_atom(num);
            let d = canon_atom(den);
            if atom_key(&d) < atom_key(&n) {
                RatioExpr::Quot { num: d, den: n }
            } else {
                RatioExpr::Quot { num: n, den: d }
            }
        }
    }
}

/// A normalized, atomic claim.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Claim {
    /// Equality of two segments/refs, e.g. `BD = DC`. Segments are stored
    /// orientation-normalized (characters sorted) so `DB` == `BD`.
    SegEq(String, String),
    /// The radius of declared circle `K` equals the length of `side`
    /// (a center-to-point segment key or another length key).
    /// Displayed as `Radius(K)=<side>`, kept unscrambled.
    RadiusEq(String, String),
    /// A predicate call bound to a value, e.g. `IsMedian(D, BC) = true`.
    PredVal { name: String, args: Vec<String>, value: Value },
    /// Incidence: a point lying on a segment/line, e.g. `On(D, BC)`.
    On(String, String),
    /// Point lies on a finite segment (used by numeric solver for segment addition).
    OnSegment(String, String),
    /// Point lies on an infinite line (used by numeric solver for Pythagoras).
    OnLine(String, String),
    /// Points on the same circle (cyclic). e.g. `OnSameCircle(A,B,C)`.
    OnSameCircle(Vec<String>),
    /// Derived from `Triangle(A,B,C,[isoscelesAt=A])`: apex of a triangle.
    IsoscelesAt(String, String),
    /// Equality of two triangles, e.g. `ABC = MNP`. Each triangle's vertices
    /// are sorted so any permutation of either side is equivalent.
    TriEq(String, String),
    /// Equality of two angles, e.g. `Angle(ABC) = Angle(MNP)`.
    AngleEq(String, String),
    /// Equality of two ratios, e.g. `BD/DC = AB/AC`. Each side is
    /// canonicalized (segments normalized, quotients inverted so the smaller
    /// atom is the numerator, and the two sides are sorted).
    RatioEq(RatioExpr, RatioExpr),
    /// A numeric length: the segment has the given length, e.g. `AD=3` or
    /// `Distance(A,H)=7`. Used by the numeric solver.
    LenEq(String, u32),
    /// A numeric squared length: the segment's square has the given value,
    /// e.g. `BH^2=32`. Internal to the numeric solver's Pythagorean steps.
    SqEq(String, u32),
}

impl Claim {
    /// Normalize a whole reference (lower-case).
    pub fn norm_ref(r: &str) -> String {
        r.to_lowercase()
    }

    /// Normalize a segment reference: lower-case and orientation-free.
    /// Supports both single-char points (e.g., "ab" -> "ab") and multi-char
    /// points with `-` delimiter (e.g., "p1-p2" -> "p1-p2").
    pub fn norm_seg(r: &str) -> String {
        let r = r.to_lowercase();
        if r.contains('-') {
            let parts: Vec<&str> = r.split('-').collect();
            if parts.len() == 2 {
                let mut pts = [parts[0], parts[1]];
                pts.sort_unstable();
                return format!("{}-{}", pts[0], pts[1]);
            }
            return r;
        }
        // Legacy: single-char points concatenated (e.g., "ab")
        let mut chars: Vec<char> = r.chars().collect();
        chars.sort_unstable();
        chars.into_iter().collect()
    }

    /// Create a segment key from two point names (orientation-free, supports multi-char).
    /// Uses `-` delimiter only for multi-char point names; single-char points are concatenated.
    pub fn seg_key(a: &str, b: &str) -> String {
        let mut a = a.to_lowercase();
        let mut b = b.to_lowercase();
        if a.len() == 1 && b.len() == 1 {
            // Single-char points: legacy concatenated format
            if b < a {
                std::mem::swap(&mut a, &mut b);
            }
            format!("{}{}", a, b)
        } else {
            // Multi-char points: use - delimiter
            let mut pts = [a, b];
            pts.sort_unstable();
            format!("{}-{}", pts[0], pts[1])
        }
    }

    /// Split a segment reference into its two endpoint names.
    /// Supports both formats: "ab" -> ["a", "b"] and "p1-p2" -> ["p1", "p2"].
    pub fn split_ref_names(seg: &str) -> Vec<String> {
        let s = seg.to_lowercase();
        if s.contains('-') {
            return s.split('-').map(|x| x.to_string()).collect();
        }
        // Legacy: single-char points
        s.chars().map(|c| c.to_string()).collect()
    }

    /// Build a segment-equality claim from raw refs.
    /// Build a point-on-circle claim: `OnCircle(P, K)`.
    pub fn on_circle(point: &str, circle: &str) -> Claim {
        Claim::pred(
            "OnCircle",
            &[Self::norm_ref(point), Self::norm_ref(circle)],
            Value::Bool(true),
        )
    }

    /// Build a segment-equality claim from raw refs. The two sides are
    /// stored in canonical (sorted) order so `WX=WY` and `WY=WX` denote the
    /// identical claim.
    pub fn seg_eq(lhs: &str, rhs: &str) -> Claim {
        let a = Self::norm_seg(lhs);
        let b = Self::norm_seg(rhs);
        if b < a {
            Claim::SegEq(b, a)
        } else {
            Claim::SegEq(a, b)
        }
    }

    /// Build a predicate claim from a raw predicate name and args.
    pub fn pred(name: &str, args: &[String], value: Value) -> Claim {
        let name = normalize_pred_name(name);
        if name == "on" && value == Value::Bool(true) && args.len() == 2 {
            // On(point, segment/line): a first-class incidence claim.
            return Claim::On(Self::norm_ref(&args[0]), Self::norm_seg(&args[1]));
        }
        // Helper: split concatenated multi-char point names like P1P2 -> [P1, P2].
        // Single-letter points (AB) are handled by norm_seg.
        fn split_multi_char_points(s: &str) -> Vec<String> {
            let s = s.to_lowercase();
            if s.len() < 2 {
                return vec![s];
            }
            // Only split if there are digits (multi-char points).
            // Pure letters like AB, BC should not be split.
            if !s.chars().any(|c| c.is_ascii_digit()) {
                return vec![s];
            }
            // Pattern: letter+digits? followed by letter+digits? (e.g., P1P2, P1Q)
            let mut result = Vec::new();
            let mut i = 0;
            while i < s.len() {
                let start = i;
                // Must start with letter
                if !s[i..].chars().next().unwrap().is_ascii_alphabetic() {
                    i += 1;
                    continue;
                }
                i += 1;
                // Consume digits
                while i < s.len() && s[i..].chars().next().unwrap().is_ascii_digit() {
                    i += 1;
                }
                result.push(s[start..i].to_string());
            }
            if result.len() >= 2 {
                result
            } else {
                vec![s]
            }
        }
        let args: Vec<String> = match name.as_str() {
            "issimilar" => {
                // Triangle references in similarity claims are
                // permutation-free, like triangle equality.
                args.iter().map(|a| Self::norm_tri(a)).collect()
            }
            "ismedian" | "isperpendicular" | "isparallel" | "isperpendicularbisector" => {
                if args.len() == 2 {
                    // For segment-ish predicates, split concatenated multi-char points first.
                    let seg1 = split_multi_char_points(&args[0]);
                    let seg2 = split_multi_char_points(&args[1]);
                    let normalized: Vec<String> = if name == "ismedian" || name == "isperpendicular" {
                        // First arg is a point (norm_ref), second is segment (norm_seg)
                        vec![
                            Self::norm_ref(&seg1.join("")),
                            Self::norm_seg(&seg2.join("-")),
                        ]
                    } else {
                        // Both args are segments
                        vec![
                            Self::norm_seg(&seg1.join("-")),
                            Self::norm_seg(&seg2.join("-")),
                        ]
                    };
                    normalized
                } else {
                    args.iter().map(|a| Self::norm_ref(a)).collect()
                }
            }
            "isaltitude" => {
                if args.len() == 2 {
                    // `IsAltitude(AH, BC)` or `IsAltitude(AH, ABC)`: the
                    // triangle form denotes the side opposite the vertex.
                    let base = if args[1].chars().count() == 3 {
                        let v = args[0].chars().next().unwrap_or(' ');
                        let opp: String = args[1]
                            .to_lowercase()
                            .chars()
                            .filter(|&c| c != v)
                            .collect();
                        if opp.chars().count() == 2 {
                            opp
                        } else {
                            args[1].clone()
                        }
                    } else {
                        args[1].clone()
                    };
                    vec![Self::norm_seg(&args[0]), Self::norm_seg(&base)]
                } else {
                    args.iter().map(|a| Self::norm_ref(a)).collect()
                }
            }
            "isanglebisector" => {
                if args.len() == 2 {
                    // A segment and an angle (vertex in the middle).
                    vec![Self::norm_seg(&args[0]), Self::norm_angle(&args[1])]
                } else {
                    args.iter().map(|a| Self::norm_ref(a)).collect()
                }
            }
            "iscentroid" | "iscircumcenter" | "isincenter" | "isorthocenter" => {
                if args.len() == 2 {
                    // A point and a triangle reference.
                    vec![Self::norm_ref(&args[0]), Self::norm_tri(&args[1])]
                } else {
                    args.iter().map(|a| Self::norm_ref(a)).collect()
                }
            }
            "onsamecircle" => {
                // OnSameCircle(A,B,C): points on the same circle.
                // Normalize points and sort for canonical representation.
                let mut pts: Vec<String> = args.iter().map(|a| Self::norm_ref(a)).collect();
                pts.sort();
                return Claim::OnSameCircle(pts);
            }
            _ => args.iter().map(|a| Self::norm_ref(a)).collect(),
        };
        Claim::PredVal { name, args, value }
    }

    /// Build a triangle-equality claim. Each triangle's vertices are
    /// lower-cased and sorted, so any permutation of either triangle denotes
    /// the same equality (`ABC=MNP` == `ACB=MPN` == ...).
    /// Build a triangle-equality claim. Vertices are normalized per side and
    /// the two sides stored in canonical (sorted) order.
    pub fn tri_eq(lhs: &str, rhs: &str) -> Claim {
        let a = Self::norm_tri(lhs);
        let b = Self::norm_tri(rhs);
        if b < a {
            Claim::TriEq(b, a)
        } else {
            Claim::TriEq(a, b)
        }
    }

    /// Normalize a triangle reference: lower-case and sort its vertices so
    /// that any permutation names the same triangle.
    pub fn norm_tri(r: &str) -> String {
        let mut chars: Vec<char> = r.to_lowercase().chars().collect();
        chars.sort_unstable();
        chars.into_iter().collect()
    }

    /// Normalize an angle reference: lower-case, keeping the vertex (middle
    /// letter) in place and sorting the two arms, so `ABC` == `CBA`.
    pub fn norm_angle(r: &str) -> String {
        let chars: Vec<char> = r.to_lowercase().chars().collect();
        if chars.len() != 3 {
            return r.to_lowercase();
        }
        let mut arms = [chars[0], chars[2]];
        arms.sort_unstable();
        let mut out = String::with_capacity(3);
        out.push(arms[0]);
        out.push(chars[1]);
        out.push(arms[1]);
        out
    }

    /// Build an angle-equality claim from raw angle refs such as `ABC`.
    /// Build an angle-equality claim. Angles are normalized per side and the
    /// two sides stored in canonical (sorted) order.
    pub fn angle_eq(lhs: &str, rhs: &str) -> Claim {
        let a = Self::norm_angle(lhs);
        let b = Self::norm_angle(rhs);
        if b < a {
            Claim::AngleEq(b, a)
        } else {
            Claim::AngleEq(a, b)
        }
    }

    /// Build a ratio-equality claim. Both sides are canonicalized so that
    /// inverted or reordered spellings denote the same claim
    /// (`BD/DC = AB/AC` == `DC/BD = AC/AB` == `AB/AC = BD/DC`).
    pub fn ratio_eq(lhs: &RatioExpr, rhs: &RatioExpr) -> Claim {
        let l = canon_ratio(lhs);
        let r = canon_ratio(rhs);
        if ratio_key(&r) < ratio_key(&l) {
            Claim::RatioEq(r, l)
        } else {
            Claim::RatioEq(l, r)
        }
    }

    /// Build a numeric length claim: `seg` has length `n`.
    pub fn len_eq(seg: &str, n: u32) -> Claim {
        Claim::LenEq(Self::norm_seg(seg), n)
    }

    /// Build a numeric squared-length claim: `seg`'s square is `n`.
    pub fn sq_eq(seg: &str, n: u32) -> Claim {
        Claim::SqEq(Self::norm_seg(seg), n)
    }

    /// True if this claim contains an unbound (empty) reference.
    pub fn has_unbound(&self) -> bool {
        match self {
            Claim::SegEq(a, b) => a.is_empty() || b.is_empty(),
            Claim::RadiusEq(c, s) => c.is_empty() || s.is_empty(),
            Claim::PredVal { args, .. } => args.iter().any(|a| a.is_empty()),
            Claim::On(p, s) => p.is_empty() || s.is_empty(),
            Claim::OnSegment(p, s) => p.is_empty() || s.is_empty(),
            Claim::OnLine(p, s) => p.is_empty() || s.is_empty(),
            Claim::OnSameCircle(pts) => pts.iter().any(|p| p.is_empty()),
            Claim::IsoscelesAt(t, a) => t.is_empty() || a.is_empty(),
            Claim::TriEq(lhs, rhs) => lhs.is_empty() || rhs.is_empty(),
            Claim::AngleEq(lhs, rhs) => lhs.is_empty() || rhs.is_empty(),
            Claim::RatioEq(lhs, rhs) => ratio_has_unbound(lhs) || ratio_has_unbound(rhs),
            Claim::LenEq(seg, _) => seg.is_empty(),
            Claim::SqEq(seg, _) => seg.is_empty(),
        }
    }
}

fn ratio_has_unbound(e: &RatioExpr) -> bool {
    match e {
        RatioExpr::Seg(s) => s.is_empty(),
        RatioExpr::Quot { num, den } => ratio_atom_unbound(num) || ratio_atom_unbound(den),
    }
}

fn ratio_atom_unbound(a: &RatioAtom) -> bool {
    match a {
        RatioAtom::Seg(s) => s.is_empty(),
        RatioAtom::Int(_) => false,
    }
}

/// Normalize a predicate name, folding documented typos into the canonical
/// spelling (e.g. `Isprependicular` -> `Isperpendicular`).
pub fn normalize_pred_name(name: &str) -> String {
    let n = name.to_lowercase();
    match n.as_str() {
        "isprependicular" => "isperpendicular".to_string(),
        "isoctuse" => "isobtuse".to_string(),
        "isrightangle" => "isright".to_string(),
        _ => n,
    }
}

/// Render a reference the way a user would write it.
fn render_ref(r: &str) -> String {
    r.to_uppercase()
}

/// Render a segment ref, orienting `expected` to line up with `goal` where
/// possible (cosmetic: used so a hint like `BD=DC` keeps the user's order).
fn orient_seg(expected: &str, goal: &str) -> String {
    let e: Vec<char> = expected.to_uppercase().chars().collect();
    let g: Vec<char> = goal.to_uppercase().chars().collect();
    if e.len() != 2 || g.len() != 2 {
        return e.into_iter().collect();
    }
    let direct = e.clone();
    let flipped = vec![e[1], e[0]];
    let score = |cands: &[char], g: &[char]| -> usize {
        cands.iter().zip(g.iter()).filter(|(a, b)| a == b).count()
    };
    let s_d = score(&direct, &g);
    let s_f = score(&flipped, &g);
    if s_f > s_d {
        flipped.into_iter().collect()
    } else if s_f == s_d && flipped[0] == g[0] {
        flipped.into_iter().collect()
    } else {
        direct.into_iter().collect()
    }
}

impl fmt::Display for Claim {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Claim::SegEq(lhs, rhs) => {
                // Without a reference orientation, render uppercase sorted.
                write!(f, "{}={}", render_ref(lhs), render_ref(rhs))
            }
            Claim::RadiusEq(circle, side) => {
                write!(f, "Radius({})={}", render_ref(circle), render_ref(side))
            }
            Claim::PredVal { name, args, value } => {
                let disp = display_predicate(name);
                let rendered_args: Vec<String> = args.iter().map(|a| render_ref(a)).collect();
                match value {
                    Value::Bool(true) => write!(f, "{}({})", disp, rendered_args.join(",")),
                    _ => write!(f, "{}({})={}", disp, rendered_args.join(","), value.render()),
                }
            }
            Claim::On(p, s) => write!(f, "On({},{})", render_ref(p), render_ref(s)),
            Claim::OnSegment(p, s) => write!(f, "OnSegment({},{})", render_ref(p), render_ref(s)),
            Claim::OnLine(p, s) => write!(f, "OnLine({},{})", render_ref(p), render_ref(s)),
            Claim::OnSameCircle(pts) => write!(f, "OnSameCircle({})", pts.iter().map(|p| render_ref(p)).collect::<Vec<_>>().join(",")),
            Claim::IsoscelesAt(t, a) => {
                write!(f, "IsoscelesAt({},{})", render_ref(t), render_ref(a))
            }
            Claim::TriEq(lhs, rhs) => {
                write!(f, "{}={}", render_ref(lhs), render_ref(rhs))
            }
            Claim::AngleEq(lhs, rhs) => {
                write!(
                    f,
                    "Angle({})=Angle({})",
                    render_ref(lhs),
                    render_ref(rhs)
                )
            }
            Claim::RatioEq(lhs, rhs) => {
                write!(f, "{} = {}", render_ratio(lhs), render_ratio(rhs))
            }
            Claim::LenEq(seg, n) => {
                let chars: Vec<char> = seg.chars().collect();
                if chars.len() == 2 {
                    let a: String = chars[0].to_uppercase().collect();
                    let b: String = chars[1].to_uppercase().collect();
                    write!(f, "Distance({},{})={}", a, b, n)
                } else {
                    write!(f, "Length({})={}", render_ref(seg), n)
                }
            }
            Claim::SqEq(seg, n) => {
                let chars: Vec<char> = seg.chars().collect();
                if chars.len() == 2 {
                    let a: String = chars[0].to_uppercase().collect();
                    let b: String = chars[1].to_uppercase().collect();
                    write!(f, "{}^2={}", format!("{}{}", a, b), n)
                } else {
                    write!(f, "Length({})^2={}", render_ref(seg), n)
                }
            }
        }
    }
}

/// Render a ratio expression the way a user would write it.
fn render_ratio(e: &RatioExpr) -> String {
    match e {
        RatioExpr::Seg(s) => render_ref(s),
        RatioExpr::Quot { num, den } => format!("{}/{}", render_atom(num), render_atom(den)),
    }
}

fn render_atom(a: &RatioAtom) -> String {
    match a {
        RatioAtom::Seg(s) => render_ref(s),
        RatioAtom::Int(n) => n.to_string(),
    }
}

impl Claim {
    /// Render a segment equality hint, orienting the expected segments to
    /// match the (incorrect) user-supplied claim for readability.
    pub fn render_hint(&self, goal: &Claim) -> String {
        match (self, goal) {
            (Claim::SegEq(el, er), Claim::SegEq(gl, gr)) => format!(
                "{}={}",
                orient_seg(el, gl),
                orient_seg(er, gr)
            ),
            _ => format!("{}", self),
        }
    }
}

/// Map a normalized predicate name to its user-facing camelCase name.
pub fn display_predicate(name: &str) -> String {
    match name {
        "isisosceles" => "IsIsosceles".into(),
        "isacute" => "IsAcute".into(),
        "isobtuse" => "IsObtuse".into(),
        "isright" => "IsRight".into(),
        "ismedian" => "IsMedian".into(),
        "issimilar" => "IsSimilar".into(),
        "isperpendicular" => "IsPerpendicular".into(),
        "isparallel" => "IsParallel".into(),
        "isanglebisector" => "IsAngleBisector".into(),
        "isaltitude" => "IsAltitude".into(),
        "iscircumcenter" => "IsCircumcenter".into(),
        "isincenter" => "IsIncenter".into(),
        "isorthocenter" => "IsOrthocenter".into(),
        "iscentroid" => "IsCentroid".into(),
        "isperpendicularbisector" => "IsPerpendicularBisector".into(),
        "isnone" => "IsNone".into(),
        "isoscelesat" => "IsoscelesAt".into(),
        "on" => "On".into(),
        "onsamecircle" => "OnSameCircle".into(),
        "oncircle" => "OnCircle".into(),
        "iscirclecenter" => "IsCircleCenter".into(),
        "isrectangle" => "IsRectangle".into(),
        "equals" => "Equals".into(),
        _ => {
            // Title-case fallback.
            let mut chars = name.chars();
            match chars.next() {
                Some(first) => first.to_uppercase().collect::<String>() + chars.as_str(),
                None => String::new(),
            }
        }
    }
}
