rule: parallelogram-opposite-sides-parallel

antecedents:
  - Parallelogram(Q)
requires:
consequent:
  - IsParallel(Seg2(A,B), Seg2(C,D))
chain:
  Parallelogram(Q)
  ->
  IsParallel(Seg2(A,B), Seg2(C,D))
