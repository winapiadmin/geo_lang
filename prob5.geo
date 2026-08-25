inp:
Triangle(A,B,C,[rightAt=A])
H=Intersection(BC,PerpendicularLine(A,BC))
prove:
1. Calc(AB), Calc(Angle(ABC))
2. OnSameCircle(A,B,C)
3. BC=AB*cos(B)+AC*cos(C)
4. IsAcute(AIK)
inp[1]:
BC=5
AC=4
inputProperties[1][Scope]=Local
inp[4]:
E=Intersection(AB,PerpendicularLine(H,AB))
I=Midpoint(BE)
K=PointOn(Ray(H,C))
HK=BI
