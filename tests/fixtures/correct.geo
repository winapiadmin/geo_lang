inp:
Triangle(A,B,C,[isoscelesAt=A])
D=Intersection(PrependicularLine(A,BC),BC)
Segment(A,D)
prove:
1. BD=DC
proof[1]:
(IsIsosceles(ABC)=true && IsPrependicular(AD,BC)) -> IsMedian(D,BC)=True -> BD=DC