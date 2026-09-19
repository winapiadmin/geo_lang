rule: rectangle-perp-feet-fh-equals-bc

antecedents:
  - IsMedian(Z, Seg2(A,C))
  - IsPerpendicular(Seg2(F,Z), Seg2(A,B))
  - IsPerpendicular(Seg2(H,Z), Seg2(C,D))
  - On(F, Seg2(A,B))
  - On(H, Seg2(C,D))
  - IsParallel(Seg2(A,B), Seg2(C,D))
requires:
  - RatioEq(Seg2(F,Z)/Seg2(A,D), 1/2)
consequent:
  - SegEq(Seg2(F,H), Seg2(B,C))
chain:
  IsMedian(Z, Seg2(A,C)) &&
  IsPerpendicular(Seg2(F,Z), Seg2(A,B)) &&
  IsPerpendicular(Seg2(H,Z), Seg2(C,D)) &&
  On(F, Seg2(A,B)) &&
  On(H, Seg2(C,D)) &&
  IsParallel(Seg2(A,B), Seg2(C,D)) &&
  RatioEq(Seg2(F,Z)/Seg2(A,D), 1/2)
  ->
  SegEq(Seg2(F,H), Seg2(B,C))
