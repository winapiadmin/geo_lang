rule: midsegment-parallel-shared-second

antecedents:
  - IsMedian(M, Seg2(A,B))
  - IsMedian(N, Seg2(B,C))
requires:
consequent:
  - IsParallel(Seg2(M,N), Seg2(A,C))
chain:
  IsMedian(M, Seg2(A,B)) &&
  IsMedian(N, Seg2(B,C))
  ->
  IsParallel(Seg2(M,N), Seg2(A,C))
