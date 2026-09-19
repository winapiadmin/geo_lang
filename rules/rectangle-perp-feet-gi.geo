rule: rectangle-perp-feet-gi-equals-ab

antecedents:
  - IsMedian(Z, Seg2(A,C))
  - IsPerpendicular(Seg2(G,Z), Seg2(B,C))
  - IsPerpendicular(Seg2(I,Z), Seg2(D,A))
  - On(G, Seg2(B,C))
  - On(I, Seg2(D,A))
  - IsParallel(Seg2(B,C), Seg2(D,A))
requires:
  - RatioEq(Seg2(G,Z)/Seg2(A,B), 1/2)
consequent:
  - SegEq(Seg2(G,I), Seg2(A,B))
chain:
  IsMedian(Z, Seg2(A,C)) &&
  IsPerpendicular(Seg2(G,Z), Seg2(B,C)) &&
  IsPerpendicular(Seg2(I,Z), Seg2(D,A)) &&
  On(G, Seg2(B,C)) &&
  On(I, Seg2(D,A)) &&
  IsParallel(Seg2(B,C), Seg2(D,A)) &&
  RatioEq(Seg2(G,Z)/Seg2(A,B), 1/2)
  ->
  SegEq(Seg2(G,I), Seg2(A,B))
