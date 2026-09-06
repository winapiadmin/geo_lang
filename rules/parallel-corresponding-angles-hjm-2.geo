rule: parallel-corresponding-angles-hjm-2

antecedents:
  - IsParallel(Seg2(M,N), Seg2(B,C))
  - On(J, Seg2(M,N))
  - On(Q2, Seg2(B,C))
  - On(M, Seg2(H,B))
requires:
consequent:
  - AngleEq(Angle(H,J,M), Angle(H,Q2,B))