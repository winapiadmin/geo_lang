rule: ratio-inversion

antecedents:
  - RatioEq(Seg2(A,B)/Seg2(C,D), Seg2(E,F)/Seg2(G,H))
requires:
consequent:
  - RatioEq(Seg2(A,B)/Seg2(E,F), Seg2(C,D)/Seg2(G,H))
chain:
  RatioEq(Seg2(A,B)/Seg2(C,D), Seg2(E,F)/Seg2(G,H))
  ->
  RatioEq(Seg2(A,B)/Seg2(E,F), Seg2(C,D)/Seg2(G,H))
