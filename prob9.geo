/*
  Random geometry problem
  -----------------------
  Isosceles triangle PQR with altitude PD to QR.

  Given:
      PD = 12
      QD = 9
      Triangle PQR is isosceles at P

  Prove:
      QD = DR
      PR^2 = 225
*/

inp:

Triangle(P,Q,R,[isoscelesAt=P])

D = Intersection(
    PerpendicularLine(P,QR),
    QR
)

Segment(P,D)
Segment(Q,D)
Segment(D,R)

Distance(P,D)=12
Distance(Q,D)=9

prove:

1. QD=DR
2. Distance(P,R)^2=225

proof[1]:
(IsIsosceles(PQR)=true && IsPerpendicular(PD,QR)) -> IsMedian(D,QR)=true -> QD=DR

proof[2]:
Distance(Q,D)=9 -> QD^2=81
Distance(P,D)=12 -> PD^2=144
(QD^2=81 && PD^2=144 && IsPerpendicular(PD,QR)) -> PR^2=225
