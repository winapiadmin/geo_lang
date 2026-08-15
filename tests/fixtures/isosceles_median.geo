inp:
Triangle(A,B,C,[isoscelesAt=A])

D=Intersection(PerpendicularLine(A,BC),BC)
Segment(A,D)

prove:
1. BD=DC

proof[1]:
(IsIsosceles(ABC)=true && IsPerpendicular(AD,BC)) -> IsMedian(D,BC)=true -> BD=DC
