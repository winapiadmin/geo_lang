inp:
Triangle(A,B,C)
H=Intersection(PerpendicularLine(C,AB),AB)
prove:
1. RightAt(CHB)=H
2. RightAt(CHA)=H
3. AH=AC*cos(A)
4. HB=BC*cos(B)
//5. BC^2=(AC*sin(A))^2+(AB-AC*cos(A))^2
5. BC^2=AB^2+AC^2-2*AB*AC*cos(A)
