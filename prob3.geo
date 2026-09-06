inp:
Triangle(A,B,C)

// H is the orthocenter
H=Orthocenter(ABC)

// Midpoints of AH, BH, CH
L=Midpoint(AH)
M=Midpoint(BH)
N=Midpoint(CH)

// Midpoints of AB, BC, CA
P=Midpoint(AB)
Q=Midpoint(BC)
R=Midpoint(CA)

// I is midpoint of LM
I=Midpoint(LM)

// J is midpoint of MN
J=Midpoint(MN)

// K is midpoint of NL
K=Midpoint(NL)

prove:
1. IsParallel(LM,AB)=true
2. IsParallel(MN,BC)=true
3. IsParallel(NL,CA)=true
4. IsParallel(PQ,AC)=true
5. IsParallel(QR,AB)=true
6. IsParallel(RP,BC)=true
/*7. IsParallel(IJ,AB)=true // FALSE! (maybe AC?)
8. IsParallel(JK,BC)=true // FALSE! (maybe AB?)
9. IsParallel(KI,CA)=true // FALSE! (maybe BC?)
10. IsCollinear(P,Q,R)=false // FALSE!
*/
7. IsParallel(IJ,AC)=true
8. IsParallel(JK,AB)=true
9. IsParallel(KI,BC)=true
10. IsCollinear(Q,J,H)=true
inp[10]:
Q2=Intersection(Line(H,J),BC)
