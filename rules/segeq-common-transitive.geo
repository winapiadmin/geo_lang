rule: segeq-common-transitive

antecedents:
  - SegEq(AnyRef(X), Seg2(A,B))
  - SegEq(AnyRef(X), Seg2(A,C))
requires:
consequent:
  - SegEq(Seg2(A,B), Seg2(A,C))
