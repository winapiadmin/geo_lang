rule: invthales-variant

antecedents:
  - On(E, Seg2(A,B))
  - On(L, Seg2(A,C))
  - RatioEq(Seg2(A,E)/Seg2(E,B), Seg2(A,L)/Seg2(L,C))
requires:
consequent:
  - IsParallel(Seg2(E,L), Seg2(B,C))
