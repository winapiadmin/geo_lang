rule: sss-similarity

antecedents:
  - SegEq(Seg2(A,B), Seg2(M,N))
  - SegEq(Seg2(B,C), Seg2(N,P))
  - SegEq(Seg2(A,C), Seg2(M,P))
requires:
consequent:
  - IsSimilar(Angle(A,B,C), Angle(M,N,P)) = true
chain:
  SegEq(Seg2(A,B), Seg2(M,N)) &&
  SegEq(Seg2(B,C), Seg2(N,P)) &&
  SegEq(Seg2(A,C), Seg2(M,P))
  ->
  IsSimilar(Angle(A,B,C), Angle(M,N,P)) = true
