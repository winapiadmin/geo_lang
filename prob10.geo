/*
============================================================================
  geo_lang mega-problem
  Covers:
    - isosceles / right / acute triangles
    - intersections and named perpendicular lines
    - midpoint / median / altitude / angle bisector
    - triangle centers
    - circles and PointOn
    - distances and squared distances
    - ratios
    - angle / triangle equality
    - rectangle predicates
    - collinearity / parallel / perpendicular
    - point-valued facts
    - indexed points
    - Calc(length) / Calc(angle)
    - IsAcute
    - trig
    - local/global proof scopes
    - Nothing
============================================================================
*/

inp:

// ==========================================================================
// Main isosceles triangle
// ==========================================================================

Triangle(A,B,C,[isoscelesAt=A])

Distance(A,B)=10
Distance(A,C)=10
Distance(B,C)=12

// Altitude from A to BC.
L_A = PerpendicularLine(A,BC)

D = Intersection(
    L_A,
    BC
)

Segment(A,D)
Segment(B,D)
Segment(D,C)

// Median / midpoint construction.
M = Midpoint(BC)

// A-angle bisector.
F = AngleBisector(A,BC)

// Other side midpoints.
P[1] = Midpoint(AB)
P[2] = Midpoint(AC)

// Midsegment joining the side midpoints.
Segment(P1,P2)

// ==========================================================================
// Circle through B,C with center M
// ==========================================================================

K = Circle(M,B)

// A point placed on the circle.
X = PointOn(K)

// Diameter endpoints B,C lie on K by construction.

// ==========================================================================
// Triangle centers
// ==========================================================================

O = Circumcenter(ABC)
I = Incenter(ABC)
H = Orthocenter(ABC)
G = Centroid(ABC)

// ==========================================================================
// Auxiliary right triangle
// ==========================================================================

Triangle(U,V,W,[rightAt=W])

Distance(U,W)=8
Distance(V,W)=6
Distance(U,V)=10

L_W = PerpendicularLine(W,UV)

// Explicit point-valued fact.
RightAt(UVW)=W

// ==========================================================================
// Auxiliary rectangle
// ==========================================================================

Segment(R,S)
Segment(S,T)
Segment(T,Q)
Segment(Q,R)

IsRectangle(R,S,T,Q)=true

// ==========================================================================
// Auxiliary similar triangles
// ==========================================================================

Triangle(J,K1,L)
Triangle(J1,K2,L1)

Distance(J,K1)=3
Distance(K1,L)=4
Distance(J,L)=5

Distance(J1,K2)=6
Distance(K2,L1)=8
Distance(J1,L1)=10

// ==========================================================================
// Explicit facts useful for the proof engine
// ==========================================================================

IsCollinear(B,D,C)=true
IsParallel(P1-P2,BC)=true
IsPerpendicular(AD,BC)=true

// The angle-bisector ratio in the isosceles triangle.
AB/AC=1/1

// Diameter / right-angle configuration.
OnSameCircle(B,X,C)=true

// Optional-valued predicate with an established value.
IsMedian(D,BC)=true

// ==========================================================================
// Goals
// ==========================================================================

prove:

// Main triangle geometry
1. BD=DC
2. Distance(A,D)^2=64
3. Distance(B,D)=6
4. BF/FC=1/1
5. P1-P2/BC=1/2

// Parallel / midpoint structure
6. IsMedian(M,BC)=true
7. IsParallel(P1-P2,BC)=true

// Circle / diameter geometry
8. Distance(M,B)=6
9. IsPerpendicular(M-X,BC)=true

// Centers
10. IsOrthocenter(H,ABC)=true
11. IsCircumcenter(O,ABC)=true
12. IsIncenter(I,ABC)=true
13. IsCentroid(G,ABC)=true

// Triangle classification
14. IsAcute(ABC)

// Right-triangle arithmetic
15. Distance(U,V)^2=100
16. Sin(Angle(UVW))=0.8
17. Cos(Angle(UVW))=0.6
18. Calc(UV)
19. Calc(Angle(U))

// Congruence / similarity
20. Triangle(ABC)=Triangle(ACB)
21. IsSimilar(JK1L,J1K2L1)=true

// Rectangle consequences
22. IsRectangle(R,S,T,Q)=true
23. IsParallel(RS,TQ)=true
24. IsParallel(ST,QR)=true
25. IsPerpendicular(RS,ST)=true

// Collinearity / point-valued facts
26. IsCollinear(B,D,C)=true
27. RightAt(UVW)=W

// A deliberately empty goal to exercise Nothing and local scope.
28. Nothing

// ==========================================================================
// Proof 1: isosceles altitude -> median -> equal halves
// ==========================================================================

proof[1]:

(IsIsosceles(ABC)=true && IsPerpendicular(AD,BC))
    -> IsMedian(D,BC)=true
    -> BD=DC

// ==========================================================================
// Proof 2: 6-8-10 from Pythagoras
// ==========================================================================

input[2]:

Distance(A,B)^2=100
Distance(B,D)^2=36
Distance(A,D)^2=64

proof[2]:
(Distance(A,D)^2=64 && Distance(B,D)^2=36)
    -> Distance(A,B)^2=100

// ==========================================================================
// Proof 3: derive BD numerically
// ==========================================================================

input[3]:

BD=DC
Distance(B,C)=12
IsCollinear(B,D,C)=true
proof[3]:
(BD=DC && Distance(B,C)=12)
    -> BD=6

// ==========================================================================
// Proof 4: angle-bisector theorem + isosceles sides
// ==========================================================================

input[4]:

Distance(A,B)=10
Distance(A,C)=10
AB/AC=1
proof[4]:
Distance(A,B)=Distance(A,C)
    -> BF/FC=AB/AC
    -> BF/FC=1

// ==========================================================================
// Proof 5: side-midpoint theorem
// ==========================================================================

input[5]:
P1 = Midpoint(AB)
P2 = Midpoint(AC)
proof[5]:


(IsMedian(P1,AB)=true && IsMedian(P2,AC)=true)
    -> IsParallel(P1-P2,BC)=true
    -> P1-P2/BC=1/2

// ==========================================================================
// Proof 6: explicit midpoint
// ==========================================================================

input[6]:

M=Midpoint(BC)
proof[6]:
IsMedian(M,BC)=true

// ==========================================================================
// Proof 7: same midsegment theorem, direct
// ==========================================================================

proof[7]:

(IsMedian(P1,AB)=true && IsMedian(P2,AC)=true)
    -> IsParallel(P1-P2,BC)=true

// ==========================================================================
// Proof 8: circle radius
// ==========================================================================

input[8]:

K=Circle(M,B)
Distance(B,C)=12
M=Midpoint(BC)

proof[8]:
IsMedian(M,BC)    -> Distance(M,B)=Distance(M,C)

Distance(B,C)=12
    -> Distance(M,B)=6

// ==========================================================================
// Proof 9: diameter / perpendicular configuration
// ==========================================================================

input[9]:

K=Circle(M,B)
OnSameCircle(B,X,C)=true
IsCollinear(B,M,C)=true
proof[9]:
OnSameCircle(B,X,C)=true
    -> IsPerpendicular(M-X,BC)=true

// ==========================================================================
// Proof 10: orthocenter construction
// ==========================================================================

input[10]:
H=Orthocenter(ABC)
proof[10]:
IsOrthocenter(H,ABC)=true

// ==========================================================================
// Proof 11: circumcenter construction
// ==========================================================================

input[11]:

O=Circumcenter(ABC)
proof[11]:
IsCircumcenter(O,ABC)=true

// ==========================================================================
// Proof 12: incenter construction
// ==========================================================================

input[12]:

I=Incenter(ABC)
proof[12]:
IsIncenter(I,ABC)=true

// ==========================================================================
// Proof 13: centroid construction
// ==========================================================================

input[13]:

G=Centroid(ABC)
proof[13]:
IsCentroid(G,ABC)=true

// ==========================================================================
// Proof 14: acute triangle via side comparison
// ==========================================================================

input[14]:

Distance(A,B)^2=100
Distance(A,C)^2=100
Distance(B,C)^2=144

// ==========================================================================
// Proof 15: 6-8-10 right triangle
// ==========================================================================

input[15]:

Distance(U,W)=8
Distance(V,W)=6
RightAt(UVW)=W
proof[15]:
Distance(U,W)^2 + Distance(V,W)^2 = Distance(U,V)^2
    -> Distance(U,V)^2=100

// ==========================================================================
// Proof 16: sine
// ==========================================================================

input[16]:

RightAt(UVW)=W
Distance(U,W)=8
Distance(U,V)=10
proof[16]:
(RightAt(UVW)=W && Distance(U,W)=8 && Distance(U,V)=10)
    -> Sin(Angle(UVW))=0.8

// ==========================================================================
// Proof 17: cosine
// ==========================================================================

input[17]:

RightAt(UVW)=W
Distance(V,W)=6
Distance(U,V)=10
proof[17]:
(RightAt(UVW)=W && Distance(V,W)=6 && Distance(U,V)=10)
    -> Cos(Angle(UVW))=0.6

// ==========================================================================
// Proof 18: Calc(length)
// ==========================================================================

proof[18]:
Nothing

// ==========================================================================
// Proof 19: Calc(angle)
// ==========================================================================

proof[19]:
Nothing

// ==========================================================================
// Proof 20: orientation-independent triangle equality
// ==========================================================================

proof[20]:

Distance(A,B)=10
Distance(A,C)=10
Distance(B,C)=12

(Distance(A,B)=Distance(A,C) && Distance(B,C)=Distance(B,C))
    -> Triangle(ABC)=Triangle(ACB)

// ==========================================================================
// Proof 21: 3-4-5 and 6-8-10 similarity
// ==========================================================================

proof[21]:

Distance(J,K1)=3
Distance(K1,L)=4
Distance(J,L)=5

Distance(J1,K2)=6
Distance(K2,L1)=8
Distance(J1,L1)=10

(JK1/K1L = J1K2/K2L1)
    -> IsSimilar(JK1L,J1K2L1)=true

// ==========================================================================
// Proof 22: rectangle is directly established by the compound predicate.
// ==========================================================================

proof[22]:

IsRectangle(R,S,T,Q)=true

// ==========================================================================
// Proof 23: rectangle -> opposite sides parallel
// ==========================================================================

proof[23]:

IsRectangle(R,S,T,Q)=true
    -> IsParallel(RS,TQ)=true

// ==========================================================================
// Proof 24: rectangle -> other opposite sides parallel
// ==========================================================================

proof[24]:

IsRectangle(R,S,T,Q)=true
    -> IsParallel(ST,QR)=true

// ==========================================================================
// Proof 25: rectangle -> adjacent sides perpendicular
// ==========================================================================

proof[25]:

IsRectangle(R,S,T,Q)=true
    -> IsPerpendicular(RS,ST)=true

// ==========================================================================
// Proof 26: explicit collinearity fact
// ==========================================================================

proof[26]:

IsCollinear(B,D,C)=true

// ==========================================================================
// Proof 27: point-valued fact
// ==========================================================================

proof[27]:

RightAt(UVW)=W

// ==========================================================================
// Proof 28: local-scope Nothing
// ==========================================================================

proofProperties[28][Scope]=Local

proof[28]:

Nothing

/*
============================================================================
  Additional parser exercises intentionally embedded above:

    - P[1] == P1
    - P[2] == P2
    - M-X / P1-P2 multi-character segment syntax
    - multiline Intersection(...)
    - named perpendicular lines
    - point-valued RightAt(...)
    - explicit Distance(A,B) and shorthand AB
    - squared lengths
    - ratios
    - predicates
    - compound rectangle
    - circle radius inherited from a point
    - local proof scope
    - Nothing
============================================================================
*/
