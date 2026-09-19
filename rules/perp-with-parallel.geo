rule: perp-with-parallel

antecedents:
  - IsParallel(Seg2(A,B), Seg2(C,D))
  - IsPerpendicular(Seg2(E,F), Seg2(C,D))
requires:
consequent:
  - IsPerpendicular(Seg2(A,B), Seg2(E,F))
chain:
  IsParallel(Seg2(A,B), Seg2(C,D)) &&
  IsPerpendicular(Seg2(E,F), Seg2(C,D))
  ->
  IsPerpendicular(Seg2(A,B), Seg2(E,F))
