rule: midsegment-parallel-shared-second

antecedents:
  - IsMedian(M, Seg2(A,B))
  - IsMedian(N, Seg2(C,B))
requires:
consequent:
  - IsParallel(Seg2(M,N), Seg2(A,C))