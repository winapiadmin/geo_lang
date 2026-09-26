rule: tangent-equal-lengths

antecedents:
  - IsPerpendicular(Seg2(A,M), Seg2(A,O))
  - IsPerpendicular(Seg2(C,M), Seg2(C,O))
  - On(A, Seg2(A,M))
  - On(C, Seg2(C,M))
requires:
consequent:
  - SegEq(Seg2(A,M), Seg2(C,M))
chain:
  IsPerpendicular(Seg2(A,M), Seg2(A,O)) &&
  IsPerpendicular(Seg2(C,M), Seg2(C,O)) &&
  On(A, Seg2(A,M)) &&
  On(C, Seg2(C,M))
  ->
  SegEq(Seg2(A,M), Seg2(C,M))
