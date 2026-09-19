rule: midsegment-parallel-shared-first

antecedents:
  - IsMedian(M, Seg2(A,B))
  - IsMedian(N, Seg2(A,C))
requires:
consequent:
  - IsParallel(Seg2(M,N), Seg2(B,C))
chain:
  IsMedian(M, Seg2(A,B)) &&
  IsMedian(N, Seg2(A,C))
  ->
  IsParallel(Seg2(M,N), Seg2(B,C))
