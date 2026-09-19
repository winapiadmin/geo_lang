// Benchmark: Coordinate geometry and midsegments
// Tests: midpoint formula, midsegment parallel

inp:
Triangle(A,B,C)
M=Midpoint(B,C)
N=Midpoint(A,C)
P=Midpoint(A,B)
prove:
1. IsParallel(MN,AB)
2. IsParallel(PN,BC)
3. Distance(B,M)=Distance(M,C)
4. Distance(A,N)=Distance(N,C)
5. Distance(A,P)=Distance(P,B)
