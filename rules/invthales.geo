rule: invthales

antecedents:
  - On(D, Seg2(A,B))
  - On(E, Seg2(A,C))
  - RatioEq(Seg2(A,D)/Seg2(D,B), Seg2(A,E)/Seg2(E,C))
requires:
consequent:
  - IsParallel(Seg2(D,E), Seg2(B,C))
