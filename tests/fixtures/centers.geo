inp:
Triangle(A,B,C)

O=Circumcenter(ABC)
I=Incenter(ABC)
H=Orthocenter(ABC)
G=Centroid(ABC)

D=Midpoint(BC)

prove:
1. OA=OB
2. IsAngleBisector(AI,BAC)=true
3. IsPerpendicular(AH,BC)
4. On(G,AD)

proof[1]:
IsCircumcenter(O,ABC) -> OA=OB

proof[2]:
IsIncenter(I,ABC) -> IsAngleBisector(AI,BAC)

proof[3]:
IsOrthocenter(H,ABC) -> IsPerpendicular(AH,BC)

proof[4]:
(IsCentroid(G,ABC) && IsMedian(D,BC)) -> On(G,AD)
