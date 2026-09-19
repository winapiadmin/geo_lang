rule: isosceles-apex-median-perpendicular

antecedents:
  - SegEq(Seg2(A,M), Seg2(A,N))
  - IsMedian(I, Seg2(M,N))
requires:
consequent:
  - IsPerpendicular(Seg2(A,I), Seg2(M,N))
chain:
  SegEq(Seg2(A,M), Seg2(A,N)) &&
  IsMedian(I, Seg2(M,N))
  ->
  IsPerpendicular(Seg2(A,I), Seg2(M,N))
