rule: midsegment-half-length-fourth

antecedents:
  - IsMedian(N, Seg2(B,C))
  - IsMedian(P, Seg2(C,D))
requires:
consequent:
  - RatioEq(Seg2(N,P)/Seg2(B,D), 1/2)
chain:
  IsMedian(N, Seg2(B,C)) &&
  IsMedian(P, Seg2(C,D))
  ->
  RatioEq(Seg2(N,P)/Seg2(B,D), 1/2)
