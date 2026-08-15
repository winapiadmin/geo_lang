inp:
Triangle(A,B,C,[isoscelesAt=A])

H = Intersection(
    PerpendicularLine(B,AC),
    PerpendicularLine(C,AB),
    PerpendicularLine(A,BC)
)

D = Intersection(PerpendicularLine(B,AC),AC)

M = Midpoint(BH)
N = Midpoint(CH)

Segment(M,N)

Distance(A,D)=7
Distance(C,D)=2

prove:
1. Distance(A,C)=9
2. Distance(A,B)=9
3. Distance(B,D)^2=32
4. Distance(B,C)^2=36
5. Distance(B,C)=6
