rule: sas-similarity

antecedents:
  - SegEq(Seg2(A,B), Seg2(M,N))
  - SegEq(Seg2(A,C), Seg2(M,P))
  - AngleEq(Angle(B,A,C), Angle(N,M,P))
requires:
consequent:
  - IsSimilar(Angle(A,B,C), Angle(M,N,P)) = true
chain:
  SegEq(Seg2(A,B), Seg2(M,N)) &&
  SegEq(Seg2(A,C), Seg2(M,P)) &&
  AngleEq(Angle(B,A,C), Angle(N,M,P))
  ->
  IsSimilar(Angle(A,B,C), Angle(M,N,P)) = true
