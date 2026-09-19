rule: parallel-corresponding-angles-hjn

antecedents:
  - IsParallel(Seg2(M,N), Seg2(B,C))
  - On(J, Seg2(M,N))
  - On(Q2, Seg2(B,C))
  - On(N, Seg2(H,C))
requires:
consequent:
  - AngleEq(Angle(H,N,J), Angle(H,C,Q2))
chain:
  IsParallel(Seg2(M,N), Seg2(B,C)) &&
  On(J, Seg2(M,N)) &&
  On(Q2, Seg2(B,C)) &&
  On(N, Seg2(H,C))
  ->
  AngleEq(Angle(H,N,J), Angle(H,C,Q2))
