rule: parallel-corresponding-angles-hjm

antecedents:
  - IsParallel(Seg2(M,N), Seg2(B,C))
  - On(J, Seg2(M,N))
  - On(Q2, Seg2(B,C))
  - On(M, Seg2(H,B))
requires:
consequent:
  - AngleEq(Angle(H,M,J), Angle(H,B,Q2))
chain:
  IsParallel(Seg2(M,N), Seg2(B,C)) &&
  On(J, Seg2(M,N)) &&
  On(Q2, Seg2(B,C)) &&
  On(M, Seg2(H,B))
  ->
  AngleEq(Angle(H,M,J), Angle(H,B,Q2))
