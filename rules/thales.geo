rule: thales

antecedents:
  - On(D, Seg2(A,B))
  - On(E, Seg2(A,C))
  - IsParallel(Seg2(D,E), Seg2(B,C))
requires:
consequent:
  - RatioEq(Seg2(A,D)/Seg2(D,B), Seg2(A,E)/Seg2(E,C))
chain:
  On(D, Seg2(A,B)) &&
  On(E, Seg2(A,C)) &&
  IsParallel(Seg2(D,E), Seg2(B,C))
  ->
  RatioEq(Seg2(A,D)/Seg2(D,B), Seg2(A,E)/Seg2(E,C))
