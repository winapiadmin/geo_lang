/*
============================================================================
  geo_lang — the .geo geometry proof language
  A self-documenting reference. This file is valid: `geo_lang check docs.geo`
  should report `proof OK`.
============================================================================

  Every line that starts with `//` (or sits inside a slash-star block) is a
  comment and
  is ignored. Everything else is real code. Use the same style to document
  your own proofs.

  A .geo file has two required sections:

      inp:    declare the geometry (triangles, points, segments, facts)
      prove:  list the goals, then prove them in `proof[N]:` blocks

  `geo_lang check <file.geo>`  validates every proof step against the built-in
  geometry rule base and reports errors/warnings with source positions.
  `geo_lang prove <file.geo>`  auto-proves every goal with the rule base, a
  numeric length/ratio/Pythagoras solver, and rational coordinate arithmetic,
  then prints a derivation chain.

  The language is case-insensitive and whitespace/indentation-insensitive:
      Prependicular == perpendicularline == PERPENDICULARLINE
  (`Prependicular` is accepted as a mis-spelling of `Perpendicular`.)

  Statements may span multiple lines while parentheses are open:

      H = Intersection(
          PerpendicularLine(B,AC),
          PerpendicularLine(C,AB)
      )

  is the same as `H = Intersection(PerpendicularLine(B,AC),PerpendicularLine(C,AB))`.
*/

inp:

// Triangle(Point,Point,Point,[TriangleProperties])
// TriangleProperties = [
//     isoscelesAt = Any | Point | None
//     acute       = Bool
//     rightAt     = Point | None
//     obtuseAt    = Point | None
// ]
// `Triangle` throws on contradictory properties:
//   throws on (!IsNone(rightAt) && !IsNone(obtuseAt))
//   throws on (acute && (!IsNone(rightAt) || !IsNone(obtuseAt)))
Triangle(A,B,C,[isoscelesAt=A])

// ---- constructions ------------------------------------------------

// Intersection(Segment|Line...) -> Point
// Takes more than one segment or line and yields their common point.
//   throws on multiple intersections (coincident operands)
//   throws on no intersection (parallel operands, detected via IsParallel facts)
// Operands may be plain segments, inline perpendicular lines, or named
// perpendicular lines (`L = PerpendicularLine(...)`, then `Intersection(L,AB)`).
D=Intersection(PrependicularLine(A,BC),BC)

// PerpendicularLine(Point,Segment) -> Line
//   `D = PerpendicularLine(A,BC)`: the line through A perpendicular to BC.
L=PerpendicularLine(A,BC)

// Midpoint(Segment) -> Point
//   `M = Midpoint(AB)`: establishes IsMedian(M,AB), On(M,AB), and AM=MB.
M=Midpoint(AB)

// AngleBisector(Point,Segment) -> Point
//   `D = AngleBisector(A,BC)`: the foot of the A-angle-bisector on BC.
//   Establishes IsAngleBisector(AD,BAC), On(D,BC), Angle(BAD)=Angle(DAC),
//   and the ratio BD/DC = AB/AC.

// Altitude(Point,Triangle|Segment) -> Segment
//   `H = Altitude(A,ABC)`: the altitude from A of triangle ABC.

// Triangle centers -> Point
//   Circumcenter(ABC), Incenter(ABC), Orthocenter(ABC), Centroid(ABC)
//   e.g. `H = Orthocenter(ABC)` establishes IsOrthocenter(H,ABC).

// PointOn(Segment) -> Point
//   `D = PointOn(AB)`: a point on segment AB (On(D,AB)).

// Segment(Point,Point) and Line(Point,Point) declare a segment/line and
// that both endpoints lie on it.
Segment(A,D)

// ---- facts --------------------------------------------------------

// Length facts: `Distance(Point,Point)=n` or `AD=n`.
Distance(A,D)=7
Distance(B,D)=6

// Two spellings, one meaning:
//   AD             the segment between points A and D (exactly 2 characters)
//   Distance(A,D)  the same length, named by its two endpoints
// Both assert the length of segment AD, produce the identical claim, and may
// be used in facts, goals, and proof steps interchangeably:
//   Distance(A,D)=7   ==   AD=7
//   Distance(B,C)^2=36 ==  BC^2=36
// `Distance(a,b)` is the explicit form — it is always clear which two points
// are meant, and it works even when you want to stress the endpoints rather
// than the segment name. The bare form `AD` is the shorthand.
// Only `Distance(a,b)` may appear as a `(...)` call inside a length
// expression; ratios accept segment references only (see below).

// Squared lengths: append `^2` to any length expression.
//   `Distance(A,B)^2=32`  `BD^2=32`  (only the exponent 2 is supported)
// Mixing a squared and a plain length on one `=` is an error:
//   `BD^2 = CE`  ->  "cannot compare a squared length with a plain length"

// Angle equality: Angle(ABC)=Angle(MNP)   (vertex in the middle)

// Triangle equality: Triangle(ABC)=Triangle(MNP)

// Predicates: Predicate(args)=Bool
//   IsParallel(seg,seg), IsPerpendicular(seg,seg), IsMedian(point,seg),
//   IsIsosceles(tri), IsSimilar(tri,tri), IsAngleBisector(seg,angle), ...
//   OnSameCircle(A,B,C)      points on one circle (any argument order)
//   IsCollinear(P,Q,R)       three collinear points
// Point-valued facts: the value after `=` may be a point name:
//   RightAt(BDH)=D           triangle BDH has its right angle at D
//   IsoscelesAt(T)=A         apex of an isosceles triangle
// Optional[T] = T | ?   (an unset value `?` throws on any equality check)
//   IsMedian(Point,Segment) -> Optional[Bool]

// Indexed points: `P[1]` and `P1` are the same identifier, so
//   P[1]=Midpoint(AB)  P[2]=Midpoint(AC)
// is equivalent to using P1 and P2 everywhere. Segments between multi-
// character points are written with a hyphen (`P1-P2`) or as
// Distance(P1,P2); inside predicates `P1P2` also works.

// Ratio equality: AD/DB=AE/EC  or  WZ/BC=1/2

// Multi-line statements are allowed (see the Intersection above).

prove:

1. BD=DC
2. Distance(A,B)^2=85

// `Nothing` is a no-op goal/proof step that does no checking.
3. Nothing

// proofProperties[N][Scope]=Local | Global
//   Local hides everything including subproofs from the enclosing scope.
//   Global (default) keeps facts visible.
proofProperties[3][Scope]=Local

proof[1]:
// A proof step is a chain of claims joined by `->`; each claim must be a fact
// already in scope, or a goal derivable by the rule base. `&&` conjoins.
// Wrong results are errors with a hint:
//   example:  IsMedian(D,BC)=true -> BD=BC
//   error:    Wrong result: IsMedian(D,BC) -> BD=BC   (hint: modify BD=BC to BD=DC)
(IsIsosceles(ABC)=true && IsPerpendicular(AD,BC)) -> IsMedian(D,BC)=true -> BD=DC

proof[2]:
// Goal 2 is numeric, so the auto-prover proves it without a proof block:
// chain: (Distance(A,D)=7 && Distance(B,D)=6) -> Distance(A,B)^2=85
Nothing

proof[3]:
// `Nothing` also skips any proof steps that follow it.
Nothing

/*
--------------------------------------------------------------------------
  Numbers, the numeric solver, and the prover
--------------------------------------------------------------------------

`geo_lang prove <file.geo>` (or `<file.geo> <claim>`) runs the auto-prover.
It forward-saturates the fact store under the rule base, then answers each
goal by join-based backward chaining; lengths/squares/ratios are derived
numerically and collinear midpoint chains by rational coordinate
arithmetic. Derivation names seen in chains and trees:

    given                  a numeric input fact (rendered [fact])
    midsegment-parallel    joining two side midpoints is parallel to the base
    midsegment-half-length WZ/BC = 1/2 for the same configuration
    thales / invthales     parallel cuts <-> proportional ratios
    perp-with-parallel     parallels share perpendiculars
    parallel-transitivity  AB||CD && CD||EF -> AB||EF
    coordinate-arithmetic  ratio equality on a line via rational coordinates
    segment-addition       AC = AH + HC            (points on a line)
    segment-subtraction
    segment-equality   swapping AB=AC / BC=AC
    isosceles-legs     AB=AC from isoscelesAt=A
    pythagoras         a^2 + b^2 = c^2
    square / sqrt      length <-> length^2 bookkeeping
    numeric-equality   two lengths equal
    numeric            ratio equality from lengths
    reflection-midpoint      RD=DA on one line makes D the midpoint of AR
    mirror-preserves-distance every point of a mirror line is equidistant
                             from a point and its mirror image

Example (see tests/fixtures/numeval1.geo):

    Distance(A,D)=7
    Distance(C,D)=2
    Triangle(A,B,C,[isoscelesAt=A])
    D=Intersection(PerpendicularLine(B,AC),AC)      // D is the foot on AC

    prove:
    3. Distance(B,D)^2=32
    4. Distance(B,C)^2=36
    5. Distance(B,C)=6

    chain for goal 3:
      (Distance(A,D)=7 && Distance(A,B)=9) -> Distance(B,D)^2=32
    chain for goal 4:
      (Distance(A,D)=7 && Distance(A,B)=9 && Distance(C,D)=2) -> BD^2=32 -> Distance(B,C)^2=36

--------------------------------------------------------------------------
  Error kinds and the -e: bypass
--------------------------------------------------------------------------

`geo_lang check <file.geo> -e:Kind1,Kind2` downgrades the listed error kinds
to assumptions (warnings with a `assumed (bypassed with -e:...)` note).
Unlisted kinds stay errors.

Kinds include: GoalNotProven, PremiseNotEstablished, WrongResult, ...

  geo_lang check docs.geo -e:GoalNotProven,PremiseNotEstablished

--------------------------------------------------------------------------
  Cheat sheet
--------------------------------------------------------------------------

Sections:
    inp:          declarations
    prove:        goals (N. claim) and proof[N]: blocks
    proofProperties[N][Scope]=Local | Global

Constructions:
    Triangle(A,B,C,[props])          Intersection(Seg|Line...)
    PerpendicularLine(P,seg)         Altitude(P,Triangle|Segment)
    Midpoint(seg)                    AngleBisector(P,seg)
    Circumcenter(tri) Incenter(tri)  Orthocenter(tri) Centroid(tri)
    PointOn(seg)                     Segment(P,P)  Line(P,P)

Facts:
    AD=3  Distance(A,D)=7            X^2=n  (squared length)
    `AD=3` and `Distance(A,D)=3` are interchangeable; both are the length of
    the segment between the two endpoints A and D.
    Angle(ABC)=Angle(MNP)            Triangle(ABC)=Triangle(MNP)
    Pred(args)=true|false            AD/DB=AE/EC   WZ/BC=1/2  (segments only)
    OnSameCircle(A,B,C)=true         IsCollinear(P,Q,R)=true
    RightAt(T)=P   (point-valued: right-angle vertex of triangle T)

Proofs:
    A -> B -> C        chain of claims
    A && B             conjunction
    Nothing            no-op (skips later steps in the block)
*/