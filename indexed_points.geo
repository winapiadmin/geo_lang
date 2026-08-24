inp:
Triangle(A,B,C)
// Indexed extra points: P[1] (== P1) is the midpoint of AB, P[2] (== P2) of AC.
P[1]=Midpoint(AB)
P[2]=Midpoint(AC)
// Midpoint of the segment P1P2.
P[3]=Midpoint(P[1],P[2])

prove:
1. IsMedian(P1,AB)=true
2. IsMedian(P2,AC)=true
3. IsParallel(P1P2,BC)=true
4. IsMedian(P3,P1P2)=true
5. On(P1,AB)=true