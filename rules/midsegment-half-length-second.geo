rule: midsegment-half-length-second

antecedents:
  - IsMedian(M, Seg2(A,B))
  - IsMedian(N, Seg2(B,C))
requires:
consequent:
  - RatioEq(Seg2(M,N)/Seg2(A,C), 1/2)
chain:
  IsMedian(M, Seg2(A,B)) &&
  IsMedian(N, Seg2(B,C))
  ->
  RatioEq(Seg2(M,N)/Seg2(A,C), 1/2)
