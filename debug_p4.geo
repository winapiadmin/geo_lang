inp:
Triangle(A,B,C)
D=Midpoint(AB)
E=Midpoint(AC)
F=Intersection(PerpendicularLine(D,BC),BC)
IsParallel(DE,BC)=true
IsPerpendicular(DF,BC)=true
prove:
1. IsPerpendicular(DE,DF)=true