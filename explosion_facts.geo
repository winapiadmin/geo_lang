inp:
O = Circle(O)
A=PointOn(O)
B=PointOn(O)
C=PointOn(O)
IsCollinear(A,O,B)
d=PerpendicularLine(C,OC)
e=PerpendicularLine(A,OA)
M=Intersection(d,e)
H=Intersection(AC,OM)
prove:
1. MA=MC
2. OA=OC=OB
3. RightAt(ABC)=C
