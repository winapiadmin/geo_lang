rule: ratio-to-similarity

antecedents:
  - RatioEq(Seg2(A,B)/Seg2(B,C), Seg2(M,N)/Seg2(N,P))
requires:
consequent:
  - IsSimilar(Tri3(A,B,C), Tri3(M,N,P)) = true
chain:
  RatioEq(Seg2(A,B)/Seg2(B,C), Seg2(M,N)/Seg2(N,P))
  ->
  IsSimilar(Tri3(A,B,C), Tri3(M,N,P)) = true
