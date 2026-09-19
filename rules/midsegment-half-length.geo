rule: midsegment-half-length

antecedents:
  - IsMedian(W, Seg2(A,B))
  - IsMedian(Z, Seg2(A,C))
requires:
consequent:
  - RatioEq(Seg2(W,Z)/Seg2(B,C), 1/2)
chain:
  IsMedian(W, Seg2(A,B)) &&
  IsMedian(Z, Seg2(A,C))
  ->
  RatioEq(Seg2(W,Z)/Seg2(B,C), 1/2)
