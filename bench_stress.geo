// Benchmark: Stress test with many goals
// Tests: forward saturation, backward chaining, rule chains

inp:
Triangle(A,B,C,[isoscelesAt=A])
M=Midpoint(B,C)
N=Midpoint(A,C)
P=Midpoint(A,B)
prove:
1. IsParallel(MN,AB)
2. IsParallel(PN,BC)
3. Distance(B,M)=Distance(M,C)
4. Distance(A,N)=Distance(N,C)
5. Distance(A,P)=Distance(P,B)
6. Distance(A,B)=Distance(A,C)
7. AB=AC
8. IsPerpendicular(AM,BC)
9. Distance(A,P)=Distance(P,B)
10. Distance(B,M)=Distance(M,C)
