rule: parallel-transitivity

antecedents:
  - IsParallel(Seg2(A,B), Seg2(C,D))
  - IsParallel(Seg2(C,D), Seg2(E,F))
requires:
consequent:
  - IsParallel(Seg2(A,B), Seg2(E,F))
chain:
  IsParallel(Seg2(A,B), Seg2(C,D)) &&
  IsParallel(Seg2(C,D), Seg2(E,F))
  ->
  IsParallel(Seg2(A,B), Seg2(E,F))
