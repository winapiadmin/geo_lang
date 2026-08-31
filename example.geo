/*
TriangleProperties = [
    isoscelesAt = Any | Point | None
    acute       = Bool
    rightAt     = Point | None
    obtuseAt    = Point | None
]
throws on
- (!IsNone(rightAt) && !IsNone(obtuseAt))
- (acute && (!IsNone(rightAt) || !IsNone(obtuseAt)))
*/
// Triangle(Point,Point,Point,TrianglesProperties)
inp:
Triangle(A,B,C,[isoscelesAt=A])
// Intersection(Line|Segment,Line|Segment)
// throws on multiple intersections
D=Intersection(PrependicularLine(A,BC),BC)
// Segment(Begin,End)
Segment(A,D)
prove:
/*
ProofProperties = [
    Scope = Local | Global // Local hides everything including subproofs
]
*/
1. BD=DC
// Nothing: does no proof ...
2. Nothing
3. Nothing
// supports spaces and case insensitive!
proofProperties[2][Scope]=Local
proof[1]:
// Optional[T] = T | ?
// throws on direct/indirect equality check with value = ?
// IsIsosceles(Triangle) -> Optional[Bool]
// IsAcute(Triangle) -> Optional[Bool]
// IsOctuse(Triangle) -> Optional[Bool]
// IsoscelesAt(Triangle) -> Any | Point | None
// IsPrependicular(Line|Segment,Line|Segment) -> Optional[Bool]
// IsMedian(Point,Segment) -> Optional[Bool]
// oopsie, i meant BD=DC, but throws it
(IsIsosceles(ABC)=true && IsPerpendicular(AD,BC)) -> IsMedian(D,BC)=True -> BD=BC
// like this:
// example.geo:42: error: Wrong result: IsMedian(D,BC) -> BD=BC
//  42 | (IsIsosceles(ABC)=true && IsPerpendicular(AD,BC)) -> IsMedian(D,BC)=True -> BD=BC
//     |                                                                             ^^^^^
// hint: modify BD=BC to BD=DC
// but Nothing also skips the proof if in the proof. :)
proof[2]:
Nothing
proof[3]:
    Nothing
    BD=BC
// indentations are also allowed!
// example.geo:53: warning: Proofs after Nothing
//  52 |     Nothing
//  53 |     BD=BC
//     |     ^^^^^
// example.geo:53: warning: Already established proof
//  52 |     Nothing
//  53 |     BD=BC
//     |     ^^^^^
// note: It was already established at proof[1]