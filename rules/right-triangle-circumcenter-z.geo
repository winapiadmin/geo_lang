rule: right-triangle-circumcenter-z

antecedents:
  - IsMedian(W, Seg2(Y,Z))
  - IsRight(AnyRef(T))
requires:
  - PredAt(RightAt, AnyRef(T), X)
consequent:
  - SegEq(Seg2(W,Z), Seg2(W,X))
chain:
  IsMedian(W, Seg2(Y,Z)) &&
  IsRight(AnyRef(T)) &&
  PredAt(RightAt, AnyRef(T), X)
  ->
  SegEq(Seg2(W,Z), Seg2(W,X))
