rule: segeq-common-transitive-rev

antecedents:
  - SegEq(Seg2(A,B), AnyRef(X))
  - SegEq(Seg2(A,C), AnyRef(X))
requires:
consequent:
  - SegEq(Seg2(A,B), Seg2(A,C))
chain:
  SegEq(Seg2(A,B), AnyRef(X)) &&
  SegEq(Seg2(A,C), AnyRef(X))
  ->
  SegEq(Seg2(A,B), Seg2(A,C))
