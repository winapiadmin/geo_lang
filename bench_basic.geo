// Benchmark: Basic triangle properties
// Tests: isosceles legs, perpendicular median, midpoint, segment equality

inp:
Triangle(A,B,C,[isoscelesAt=A])
M=Midpoint(B,C)
prove:
1. Distance(A,B)=Distance(A,C)
2. IsPerpendicular(AM,BC)
3. Distance(B,M)=Distance(M,C)
4. AB=AC
