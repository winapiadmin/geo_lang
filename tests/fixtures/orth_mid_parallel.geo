inp:
Triangle(A,B,C,[acute=true])

H = Orthocenter(ABC)

D = Intersection(PerpendicularLine(B,AC),AC)
E = Intersection(PerpendicularLine(C,AB),AB)

M = Midpoint(BC)
N = Midpoint(BH)
P = Midpoint(CH)

Segment(D,E)
Segment(M,N)
Segment(M,P)

prove:
1. IsPerpendicular(AH,BC)
2. IsPerpendicular(BH,AC)
3. IsPerpendicular(CH,AB)

4. IsMedian(M,BC)
5. IsMedian(N,BH)
6. IsMedian(P,CH)

7. IsParallel(MN,CH)
8. IsParallel(MP,BH)

9. MN/CH=1/2
10. MP/BH=1/2
