rule: parallelogram-diagonals-bisect

antecedents:
  - Parallelogram(Q)
requires:
consequent:
  - IsMedian(O, Seg2(A,C))
chain:
  Parallelogram(Q)
  ->
  IsMedian(O, Seg2(A,C))
