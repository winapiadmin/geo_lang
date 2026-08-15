inp:
Triangle(A,B,C)

W=Midpoint(AB)
Z=Midpoint(AC)

prove:
1. IsParallel(WZ,BC)
2. WZ/BC=1/2

proof[1]:
(IsMedian(W,AB) && IsMedian(Z,AC)) -> IsParallel(WZ,BC)

proof[2]:
(IsMedian(W,AB) && IsMedian(Z,AC)) -> WZ/BC=1/2
