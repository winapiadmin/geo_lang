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
/*proof[3]:
AZ=BZ=CZ=DZ -> AZ^2=BZ^2=CZ^2=DZ^2 -> AZ^2+BZ^2+CZ^2+DZ^2=4*AZ^2
RightAt(ABC)=B -> AB^2+BC^2=AC^2=(2*AZ)^2=4*AZ^2
-> AZ^2+BZ^2+CZ^2+DZ^2=AB^2+BC^2+AC^2*/
prove:
9. IsMedian(F,AB)
/*proof[9]:
(IsPerpendicular(FZ,AB)=true && IsPerpendicular(BC,AB)=true) -> IsParallel(FZ,BC)=true
(IsParallel(FZ,BC)=true && IsMedian(Z,AC)=true) -> IsMedian(F,AB)=true
*/
// Disabled 1 rule(s): rectangle-perp-feet-fh-equals-bc, rectangle-perp-feet-gi-equals-ab
proof[1]:
// OnSameCircle(A,B,C,D)  [fact]
OnSameCircle(A,B,C,D)
proof[2]:
// AZ=BZ
//   by ratio-segeq:
//   AZ/BZ = DZ/CZ  [fact]
//   BZ/AZ = DZ/CZ  [fact]
(AZ/BZ = DZ/CZ && BZ/AZ = DZ/CZ) -> AZ=BZ
// BZ=CZ
//   by ratio-segeq:
//   BZ/CZ = DZ/AZ  [fact]
//   CZ/BZ = DZ/AZ  [fact]
(BZ/CZ = DZ/AZ && CZ/BZ = DZ/AZ) -> BZ=CZ
// CZ=DZ  [fact]
CZ=DZ
proof[3]:
// AZ^2+BZ^2+CZ^2+DZ^2=AB^2+BC^2
//   by rectangle-diagonal-identity:
//   Eqchain(AZ^2+BZ^2+CZ^2+DZ^2=4*AZ^2)
//     by rectangle-equidistant:
//   Eqchain(AB^2+BC^2=AC^2)
//     by pythagoras:
//   Eqchain(AC=2*AZ)
//     by midpoint-diagonal:
AZ^2+BZ^2+CZ^2+DZ^2=AB^2+BC^2
proof[4]:
// MN=NP  [fact]
MN=NP
// NP=PQ  [fact]
NP=PQ
// MQ=PQ  [fact]
PQ=QM
proof[5]:
// Intersection(MP,NQ)=Z
//   by midpoint-diagonals-intersection:
//   IsMedian(M,AB)  [fact]
//   IsMedian(N,BC)  [fact]
//   IsMedian(P,CD)  [fact]
//   IsMedian(Q,AD)  [fact]
//   IsMedian(Z,AC)  [fact]
//   IsMedian(Z,BD)  [fact]
(IsMedian(M,AB) && IsMedian(N,BC) && IsMedian(P,CD) && IsMedian(Q,AD) && IsMedian(Z,AC) && IsMedian(Z,BD)) -> Intersection(MP,NQ)=Z
proof[6]:
// FG=GH  [fact]
FG=GH
// GH=HI  [fact]
GH=HI
// FI=HI  [fact]
HI=IF
proof[7]:
// FH=BC
//   by fallback-chain:
//   IsMedian(Z,AC)  [fact]
//   IsPerpendicular(FZ,AB)
//     by isosceles-apex-median-perpendicular:
//     AZ=BZ  [fact]
//     IsMedian(F,AB)  [fact]
//   IsPerpendicular(HZ,CD)
//     by isosceles-apex-median-perpendicular:
//     CZ=DZ  [fact]
//     IsMedian(H,CD)  [fact]
//   On(F,AB)
//     by median-implies-on:
//     IsMedian(F,AB)  [fact]
//   On(H,CD)
//     by median-implies-on:
//     IsMedian(H,CD)  [fact]
//   IsParallel(AB,CD)
//     by parallel-transitivity:
//     IsParallel(AB,GZ)
//       by invthales:
//       On(G,BC)  [fact]
//       On(Z,AC)  [fact]
//       CG/BG = CZ/AZ
//         by coordinate-arithmetic:
//     IsParallel(CD,GZ)
//       by invthales:
//       On(G,BC)  [fact]
//       On(Z,BD)  [fact]
//       BG/CG = BZ/DZ
//         by coordinate-arithmetic:
//   1/2 = FZ/AD
//     by midsegment-half-length:
//     IsMedian(F,AB)  [fact]
//     IsMedian(Z,BD)  [fact]
(AZ=BZ && IsMedian(F,AB)) -> IsPerpendicular(FZ,AB)
(CZ=DZ && IsMedian(H,CD)) -> IsPerpendicular(HZ,CD)
IsMedian(F,AB) -> On(F,AB)
IsMedian(H,CD) -> On(H,CD)
(On(G,BC) && On(Z,AC) && CG/BG = CZ/AZ) -> IsParallel(AB,GZ)
(On(G,BC) && On(Z,BD) && BG/CG = BZ/DZ) -> IsParallel(CD,GZ)
(IsParallel(AB,GZ) && IsParallel(CD,GZ)) -> IsParallel(AB,CD)
(IsMedian(F,AB) && IsMedian(Z,BD)) -> 1/2 = FZ/AD
(IsMedian(Z,AC) && IsPerpendicular(FZ,AB) && IsPerpendicular(HZ,CD) && On(F,AB) && On(H,CD) && IsParallel(AB,CD) && 1/2 = FZ/AD) -> FH=BC
proof[8]:
// GI=AB
//   by fallback-chain:
//   IsMedian(Z,BD)  [fact]
//   IsPerpendicular(IZ,AD)
//     by isosceles-apex-median-perpendicular:
//     AZ=DZ  [fact]
//     IsMedian(I,AD)  [fact]
//   IsPerpendicular(GZ,BC)
//     by isosceles-apex-median-perpendicular:
//     BZ=CZ  [fact]
//     IsMedian(G,BC)  [fact]
//   On(I,AD)
//     by median-implies-on:
//     IsMedian(I,AD)  [fact]
//   On(G,BC)
//     by median-implies-on:
//     IsMedian(G,BC)  [fact]
//   IsParallel(AD,BC)
//     by parallel-transitivity:
//     IsParallel(AD,FZ)
//       by invthales:
//       On(F,AB)  [fact]
//       On(Z,BD)  [fact]
//       BF/AF = BZ/DZ
//         by coordinate-arithmetic:
//     IsParallel(BC,FZ)
//       by invthales:
//       On(F,AB)  [fact]
//       On(Z,AC)  [fact]
//       AF/BF = AZ/CZ
//         by coordinate-arithmetic:
//   1/2 = IZ/CD
//     by midsegment-half-length:
//     IsMedian(I,AD)  [fact]
//     IsMedian(Z,AC)  [fact]
(AZ=DZ && IsMedian(I,AD)) -> IsPerpendicular(IZ,AD)
(BZ=CZ && IsMedian(G,BC)) -> IsPerpendicular(GZ,BC)
IsMedian(I,AD) -> On(I,AD)
IsMedian(G,BC) -> On(G,BC)
(On(F,AB) && On(Z,BD) && BF/AF = BZ/DZ) -> IsParallel(AD,FZ)
(On(F,AB) && On(Z,AC) && AF/BF = AZ/CZ) -> IsParallel(BC,FZ)
(IsParallel(AD,FZ) && IsParallel(BC,FZ)) -> IsParallel(AD,BC)
(IsMedian(I,AD) && IsMedian(Z,AC)) -> 1/2 = IZ/CD
(IsMedian(Z,BD) && IsPerpendicular(IZ,AD) && IsPerpendicular(GZ,BC) && On(I,AD) && On(G,BC) && IsParallel(AD,BC) && 1/2 = IZ/CD) -> GI=AB
proof[9]:
// IsMedian(F,AB)
//   by iso-altitude-bisects:
//   AM=BM  [fact]
//   IsPerpendicular(AB,FM)
//     by isosceles-apex-median-perpendicular:
//     AF=BF
//       by ratio-segeq:
//       AF/BC = FZ/AB  [fact]
//       BF/AD = FZ/AB  [fact]
//     IsMedian(M,AB)  [fact]
//   On(F,AB)  [fact]
(AF/BC = FZ/AB && BF/AD = FZ/AB) -> AF=BF
(AF=BF && IsMedian(M,AB)) -> IsPerpendicular(AB,FM)
(AM=BM && IsPerpendicular(AB,FM) && On(F,AB)) -> IsMedian(F,AB)