rule: similar-triangles-proportional-sides

antecedents:
  - IsSimilar(Tri3(A,B,C), Tri3(M,N,P))
requires:
consequent:
  - RatioEq(Seg2(A,B)/Seg2(M,N), Seg2(A,C)/Seg2(M,P))
chain:
  IsSimilar(Tri3(A,B,C), Tri3(M,N,P))
  ->
  RatioEq(Seg2(A,B)/Seg2(M,N), Seg2(A,C)/Seg2(M,P))
