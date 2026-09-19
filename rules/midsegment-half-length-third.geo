rule: midsegment-half-length-third

antecedents:
  - IsMedian(M, Seg2(A,C))
  - IsMedian(N, Seg2(B,C))
requires:
consequent:
  - RatioEq(Seg2(M,N)/Seg2(A,B), 1/2)
chain:
  IsMedian(M, Seg2(A,C)) &&
  IsMedian(N, Seg2(B,C))
  ->
  RatioEq(Seg2(M,N)/Seg2(A,B), 1/2)
