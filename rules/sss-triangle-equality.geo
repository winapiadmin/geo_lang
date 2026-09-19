rule: sss-triangle-equality

antecedents:
  - SegEq(Seg2(A,B), Seg2(M,N))
  - SegEq(Seg2(B,C), Seg2(N,P))
  - SegEq(Seg2(A,C), Seg2(M,P))
requires:
consequent:
  - TriEq(Angle(A,B,C), Angle(M,N,P))
chain:
  SegEq(Seg2(A,B), Seg2(M,N)) &&
  SegEq(Seg2(B,C), Seg2(N,P)) &&
  SegEq(Seg2(A,C), Seg2(M,P))
  ->
  TriEq(Angle(A,B,C), Angle(M,N,P))
