inp:
Triangle(A,B,C)

// H is the orthocenter
H=Intersection(PerpendicularLine(A,BC),PerpendicularLine(B,AC))

// D is the foot of the altitude from A
D=Intersection(PerpendicularLine(A,BC),BC)

// E is the foot of the altitude from B
E=Intersection(PerpendicularLine(B,AC),AC)

// F is the foot of the altitude from C
F=Intersection(PerpendicularLine(C,AB),AB)

// Reflect H across AB
R=PointOn(Line(H,F))
RF=HF

// Reflect H across AC
S=PointOn(Line(H,E))
SE=HE

// I is midpoint of RS
I=Midpoint(RS)

// J is midpoint of EF
J=Midpoint(EF)

// K is midpoint of BC
K=Midpoint(BC)

// L is midpoint of AH
L=Midpoint(AH)

// M is midpoint of BH
M=Midpoint(BH)

// N is midpoint of CH
N=Midpoint(CH)

prove:
/*1. IsParallel(RS,BC)=true
2. IsParallel(EF,MN)=true
3. IsParallel(LM,AB)=true
4. IsParallel(LN,AC)=true
5. IsPerpendicular(IJ,AH)=true
6. IsPerpendicular(IK,EF)=true*/
1. IsParallel(LM,AB)=true
2. IsParallel(LN,AC)=true
