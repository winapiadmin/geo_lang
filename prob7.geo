inp:
Rectangle(A,B,C,D)
Z=Intersection(AC,BD)
prove:
1. OnSameCircle(A,B,C,D)
2. AZ=BZ=CZ=DZ
3. AZ^2+BZ^2+CZ^2+DZ^2=AB^2+BC^2
inp[4]:
M=Midpoint(AB)
N=Midpoint(BC)
P=Midpoint(CD)
Q=Midpoint(DA)
inp[6]:
F=Intersection(AB,PerpendicularlIne(Z,AB))
G=Intersection(BC,PerpendicularlIne(Z,BC))
H=Intersection(CD,PerpendicularlIne(Z,CD))
I=Intersection(DA,PerpendicularlIne(Z,DA))
prove:
4. MN=NP=PQ=QM
5. Intersection(MP,NQ)=Z
6. FG=GH=HI=IF
7. FH=BC
8. GI=AB
proof[3]:
AZ=BZ=CZ=DZ -> AZ^2=BZ^2=CZ^2=DZ^2 -> AZ^2+BZ^2+CZ^2+DZ^2=4*AZ^2
RightAt(ABC)=B -> AB^2+BC^2=AC^2=(2*AZ)^2=4*AZ^2
-> AZ^2+BZ^2+CZ^2+DZ^2=AB^2+BC^2+AC^2
prove:
9. IsMedian(F,AB)
proof[9]:
(IsPerpendicular(FZ,AB)=true && IsPerpendicular(BC,AB)=true) -> IsParallel(FZ,BC)=true
(IsParallel(FZ,BC)=true && IsMedian(Z,AC)=true) -> IsMedian(F,AB)=true
