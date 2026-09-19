rule: parallel-corresponding-angles-hjn-2

antecedents:
  - IsParallel(Seg2(M,N), Seg2(B,C))
  - On(J, Seg2(M,N))
  - On(Q2, Seg2(B,C))
  - On(N, Seg2(H,C))
requires:
consequent:
  - AngleEq(Angle(H,J,N), Angle(H,Q2,C))
chain:
  IsParallel(Seg2(M,N), Seg2(B,C)) &&
  On(J, Seg2(M,N)) &&
  On(Q2, Seg2(B,C)) &&
  On(N, Seg2(H,C))
  ->
  AngleEq(Angle(H,J,N), Angle(H,Q2,C))
