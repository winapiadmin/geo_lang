rule: midsegment-parallel-general

antecedents:
  - IsMedian(M, Seg2(X,H))
  - IsMedian(N, Seg2(Y,H))
requires:
consequent:
  - IsParallel(Seg2(M,N), Seg2(X,Y))
chain:
  IsMedian(M, Seg2(X,H)) &&
  IsMedian(N, Seg2(Y,H))
  ->
  IsParallel(Seg2(M,N), Seg2(X,Y))
