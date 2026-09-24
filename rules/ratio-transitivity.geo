rule: ratio-transitivity

antecedents:
  - RatioEq(Seg2(A,B)/Seg2(C,D), Seg2(E,F)/Seg2(G,H))
  - RatioEq(Seg2(E,F)/Seg2(G,H), Seg2(I,J)/Seg2(K,L))
consequent:
  - RatioEq(Seg2(A,B)/Seg2(C,D), Seg2(I,J)/Seg2(K,L))
