rule: midsegment-half-length-fifth

antecedents:
  - IsMedian(P, Seg2(C,D))
  - IsMedian(Q, Seg2(A,D))
requires:
consequent:
  - RatioEq(Seg2(P,Q)/Seg2(A,C), 1/2)
chain:
  IsMedian(P, Seg2(C,D)) &&
  IsMedian(Q, Seg2(A,D))
  ->
  RatioEq(Seg2(P,Q)/Seg2(A,C), 1/2)
