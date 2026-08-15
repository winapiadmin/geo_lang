inp:
Triangle(A,B,C)
// AH ⟂ BC
H=Intersection(PerpendicularLine(A,BC),BC)
// HE ⟂ AB, E ∈ AB
E=Intersection(PerpendicularLine(H,AB),AB)
// M is on the extension of HE and ME = HE
M=PointOn(Line(H,E))
ME=HE
// HF ⟂ AC, F ∈ AC
F=Intersection(PerpendicularLine(H,AC),AC)
// N is on the extension of HF and FN = FH
N=PointOn(Line(H,F))
FN=FH
// I is the midpoint of MN
I=Midpoint(MN)
prove:
1. IsParallel(EF,MN)=true
2. IsPerpendicular(AI,EF)=true
