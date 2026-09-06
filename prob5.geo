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
inp[4]:
E=Intersection(AB,PerpendicularLine(H,AB))
I=Midpoint(BE)
K=PointOn(Ray(H,C))
HK=BI
proof[1]:
(RightAt(ABC)=A) -> AB^2+AC^2=BC^2 -> AB=sqrt(BC^2-AC^2)=3 -> Angle(ABC)=Angle(ABC)
proof[2]:
RightAt(ABC)=A -> OnSameCircle(A,B,C)
proof[3]:
AB*cos(B)=AB*AB/BC
AC*cos(C)=AC*AC/BC
AB*cos(B)+AC*cos(C)=AB^2/BC+AC^2/BC=(AB^2+AC^2)/BC=BC^2/BC=BC