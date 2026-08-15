inp:
Triangle(A,B,C,[isoscelesAt=A])
//H=Intersection(PerpendicularLine(A,BC),BC)
//or
//Altitude(Point,Triangle)
H=Altitude(A,ABC)
Segment(A,H)

prove:
// IsAltitude(Segment,Triangle)
1. IsAltitude(AH,ABC)
2. IsMedian(H,BC)
3. IsAngleBisector(AH,Angle(BAC))
// IsPrependicularBisector(Segment,Segment)
4. IsPerpendicularBisector(AH,BC)
