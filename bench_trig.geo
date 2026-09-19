// Benchmark: Trigonometric relationships
// Tests: cos definition, Pythagorean theorem, angle calculations

inp:
Triangle(A,B,C,[rightAt=A])
Distance(A,B)=3
Distance(A,C)=4
Distance(B,C)=5
prove:
1. Calc(AB)
2. Calc(Angle(ABC))
3. Calc(Angle(ACB))
4. BC^2=AB^2+AC^2
