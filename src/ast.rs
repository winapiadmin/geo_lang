//! Abstract syntax tree for `.geo` files.

use crate::claim::{RatioExpr, Value};

/// A source position (1-based line and column).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Pos {
    pub line: usize,
    pub col: usize,
}

/// A length expression: either a raw segment reference (`BD`) or a
/// `Distance(Point, Point)` call. Used on both sides of `=` in claims.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LenExpr {
    Seg(String),
    Distance(String, String),
    /// A numeric literal, e.g. the `7` in `Distance(A,H)=7` or `AD=3`.
    Num(u32),
    /// A squared length expression, e.g. the `Distance(B,D)^2` in
    /// `Distance(B,D)^2=32`.
    Sq(Box<LenExpr>),
}

impl LenExpr {
    /// The segment reference this length expression denotes (empty for a
    /// numeric literal).
    pub fn seg(&self) -> String {
        match self {
            LenExpr::Seg(r) => r.clone(),
            LenExpr::Distance(a, b) => format!("{}{}", a, b),
            LenExpr::Num(_) => String::new(),
            LenExpr::Sq(inner) => inner.seg(),
        }
    }

    pub fn is_num(&self) -> bool {
        match self {
            LenExpr::Num(_) => true,
            LenExpr::Sq(inner) => inner.is_num(),
            _ => false,
        }
    }

    /// Whether this expression is wrapped in `^2`.
    pub fn squared(&self) -> bool {
        matches!(self, LenExpr::Sq(_))
    }

    pub fn numeric(&self) -> Option<u32> {
        match self {
            LenExpr::Num(n) => Some(*n),
            LenExpr::Sq(inner) => inner.numeric().and_then(|n| n.checked_mul(n)),
            _ => None,
        }
    }
}

/// An expression appearing in a proof: a single claim or a chain of claims
/// joined by `->`.
#[derive(Debug, Clone)]
pub enum ClaimExpr {
    /// An equality (possibly chained) of length expressions, e.g.
    /// `BD=DC` or `Distance(B,D)=Distance(C,D)=Distance(A,D)`.
    EqChain { items: Vec<LenExpr>, pos: Pos },
    PredEq {
        name: String,
        args: Vec<String>,
        value: Value,
        pos: Pos,
    },
    PredCall {
        name: String,
        args: Vec<String>,
        pos: Pos,
    },
    /// A parenthesized conjunction such as `(A && B)` used as a premise.
    Conj { items: Vec<ClaimExpr>, pos: Pos },
    /// Equality of two triangles, e.g. `ABC = MNP`. The user's vertex order
    /// is preserved for display; semantically, permutations of either side
    /// are equivalent.
    TriEq { lhs: String, rhs: String, pos: Pos },
    /// Equality of two triangles written with the `Triangle(...)` wrapper,
    /// e.g. `Triangle(ABC)=Triangle(MNP)` (used to disambiguate from angle
    /// equalities such as `Angle(ABC)=Angle(MNP)`).
    TriCall { lhs: String, rhs: String, pos: Pos },
    /// Equality of two angles, e.g. `Angle(ABC)=Angle(MNP)`.
    AngleEq { lhs: String, rhs: String, pos: Pos },
    /// Equality of two ratios, e.g. `BD/DC = AB/AC`.
    RatioEq {
        lhs: RatioExpr,
        rhs: RatioExpr,
        pos: Pos,
    },
}

impl ClaimExpr {
    pub fn pos(&self) -> Pos {
        match self {
            ClaimExpr::EqChain { pos, .. }
            | ClaimExpr::PredEq { pos, .. }
            | ClaimExpr::PredCall { pos, .. }
            | ClaimExpr::Conj { pos, .. }
            | ClaimExpr::TriEq { pos, .. }
            | ClaimExpr::TriCall { pos, .. }
            | ClaimExpr::AngleEq { pos, .. }
            | ClaimExpr::RatioEq { pos, .. } => *pos,
        }
    }
}

/// A geometry construction used in the input section.
#[derive(Debug, Clone)]
pub enum Geom {
    Ref(String),
    /// The common point of 2+ segments/lines, e.g.
    /// `O = Intersection(AB, BC, PerpendicularLine(A, BC))`.
    /// Throws when the operands are parallel (no intersection) or coincident
    /// (multiple intersections).
    Intersection(Vec<Geom>, Pos),
    PerpendicularLine {
        point: String,
        base: String,
        pos: Pos,
    },
    /// The line through `point` parallel to `base`, e.g. `L = ParallelLine(A, BC)`.
    /// Throws when `point` already lies on `base` (the line would be undefined).
    ParallelLine {
        point: String,
        base: String,
        pos: Pos,
    },
    Midpoint {
        a: String,
        b: String,
        pos: Pos,
    },
    /// The foot where the angle bisector at `vertex` meets the opposite
    /// segment `base`, e.g. `D = AngleBisector(A, BC)`.
    AngleBisector {
        vertex: String,
        base: String,
        pos: Pos,
    },
    /// The perpendicular foot from `vertex` to `base`,
    /// e.g. `H = Altitude(A, BC)`.
    Altitude {
        vertex: String,
        base: String,
        pos: Pos,
    },
    /// A triangle center: circumcenter/incenter/orthocenter/centroid.
    Center {
        kind: CenterKind,
        tri: String,
        pos: Pos,
    },
    /// An infinite line through two points, e.g. `L = Line(A, B)` or the
    /// operand of `PointOn(Line(A, B))`.
    Line {
        a: String,
        b: String,
        pos: Pos,
    },
    /// An arbitrary point on a segment or line, e.g. `D = PointOn(AB)` or
    /// `M = PointOn(Line(H, E))`. `line_pts` is set when the operand was an
    /// explicit `Line(a, b)` (so the endpoints are also known to lie on it).
    PointOn {
        seg: String,
        line_pts: Option<(String, String)>,
        pos: Pos,
    },
    /// A declared circle: `K = Circle(O)`, `K = Circle(O, 7)`,
    /// `K = Circle(O, AB)` (radius equal to length AB), or
    /// `K = Circle(O, P)` (circle through point P, i.e. radius OP).
    Circle {
        center: String,
        radius: Option<RadiusSpec>,
        pos: Pos,
    },
}

/// The radius part of a `Circle` declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RadiusSpec {
    /// Numeric radius: `Circle(O, 7)`.
    Num(u32),
    /// Radius equal to a segment length: `Circle(O, AB)`.
    Seg(String),
    /// Circle through a point: `Circle(O, P)` — radius is OP and P lies on it.
    ThroughPoint(String),
}

/// The kind of a triangle-center construction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CenterKind {
    Circumcenter,
    Incenter,
    Orthocenter,
    Centroid,
}

impl Geom {
    #[allow(dead_code)]
    pub fn pos(&self) -> Pos {
        match self {
            Geom::Ref(_) => Pos { line: 0, col: 0 },
            Geom::Intersection(_, pos)
            | Geom::PerpendicularLine { pos, .. }
            | Geom::ParallelLine { pos, .. }
            | Geom::Midpoint { pos, .. }
            | Geom::AngleBisector { pos, .. }
            | Geom::Altitude { pos, .. }
            | Geom::Center { pos, .. }
            | Geom::Line { pos, .. }
            | Geom::PointOn { pos, .. }
            | Geom::Circle { pos, .. } => *pos,
        }
    }
}

/// An input-section statement.
#[derive(Debug, Clone)]
pub enum InputStmt {
    Triangle {
        name: String,
        points: Vec<String>,
        props: Vec<(String, Value)>,
        pos: Pos,
    },
    Assign {
        name: String,
        geom: Geom,
        pos: Pos,
    },
    Segment {
        a: String,
        b: String,
        pos: Pos,
    },
    Line {
        a: String,
        b: String,
        pos: Pos,
    },
    /// A (possibly chained) equality of length expressions in the input
    /// section, e.g. `AB=MN` or `AM=BN=CP`.
    EqChain {
        items: Vec<LenExpr>,
        pos: Pos,
    },
    /// Equality of two angles in the input section, e.g.
    /// `Angle(ABC)=Angle(MNP)`.
    AngleEq {
        lhs: String,
        rhs: String,
        pos: Pos,
    },
    /// A predicate fact asserted in the input section, e.g.
    /// `IsAngleBisector(AD,BAC)=true` or `On(D,BC)=true`.
    PredFact {
        name: String,
        args: Vec<String>,
        value: Value,
        pos: Pos,
    },
    /// A ratio equality in the input section, e.g. `BD/DC = AB/AC`.
    RatioEq {
        lhs: RatioExpr,
        rhs: RatioExpr,
        pos: Pos,
    },
}

impl InputStmt {
    #[allow(dead_code)]
    pub fn pos(&self) -> Pos {
        match self {
            InputStmt::Triangle { pos, .. }
            | InputStmt::Assign { pos, .. }
            | InputStmt::Segment { pos, .. }
            | InputStmt::Line { pos, .. }
            | InputStmt::EqChain { pos, .. }
            | InputStmt::AngleEq { pos, .. }
            | InputStmt::PredFact { pos, .. }
            | InputStmt::RatioEq { pos, .. } => *pos,
        }
    }
}

/// A numbered goal from the `prove:` section, e.g. `1. BD=DC`.
#[derive(Debug, Clone)]
pub struct Goal {
    pub index: u32,
    pub claim: Option<ClaimExpr>,
    #[allow(dead_code)]
    pub pos: Pos,
}

/// Proof visibility scope.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Scope {
    /// Everything from other proofs and global facts is hidden.
    Local,
    /// Global facts are visible (default).
    Global,
}

/// `proofProperties[N][Scope]=Local` style declaration.
#[derive(Debug, Clone)]
pub struct ProofProp {
    pub index: u32,
    pub scope: Scope,
    #[allow(dead_code)]
    pub pos: Pos,
}

/// A step inside a proof block.
#[derive(Debug, Clone)]
pub enum Step {
    /// `Nothing` - does no proof, and skips the rest of the proof.
    #[allow(dead_code)]
    Nothing(Pos),
    /// A claim or implication chain, e.g. `A -> B -> C`.
    Chain { claims: Vec<ClaimExpr>, pos: Pos },
}

impl Step {
    #[allow(dead_code)]
    pub fn pos(&self) -> Pos {
        match self {
            Step::Nothing(p) => *p,
            Step::Chain { pos, .. } => *pos,
        }
    }
}

/// A `proof[N]:` block.
#[derive(Debug, Clone)]
pub struct ProofBlock {
    pub index: u32,
    pub steps: Vec<Step>,
    #[allow(dead_code)]
    pub pos: Pos,
}

/// A fully parsed `.geo` file.
#[derive(Debug, Clone)]
pub struct File {
    /// Path of the source file, used in diagnostics.
    #[allow(dead_code)]
    pub source: String,
    /// Raw source lines for diagnostic display.
    pub lines: Vec<String>,
    pub input: Vec<InputStmt>,
    pub goals: Vec<Goal>,
    pub props: Vec<ProofProp>,
    pub proofs: Vec<ProofBlock>,
}
