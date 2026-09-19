rule: median-implies-on

antecedents:
  - IsMedian(M, Seg2(A,B)) = true
requires:
consequent:
  - On(M, Seg2(A,B))
chain:
  IsMedian(M, Seg2(A,B)) = true
  ->
  On(M, Seg2(A,B))
