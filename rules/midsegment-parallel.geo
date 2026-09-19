rule: midsegment-parallel

antecedents:
  - IsMedian(W, Seg2(A,B))
  - IsMedian(Z, Seg2(A,C))
requires:
consequent:
  - IsParallel(Seg2(W,Z), Seg2(B,C))
chain:
  IsMedian(W, Seg2(A,B)) &&
  IsMedian(Z, Seg2(A,C))
  ->
  IsParallel(Seg2(W,Z), Seg2(B,C))
