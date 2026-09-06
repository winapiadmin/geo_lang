rule: right-triangle-circumcenter-y

antecedents:
  - IsMedian(W, Seg2(Y,Z))
  - IsRight(AnyRef(T))
requires:
  - PredAt(RightAt, AnyRef(T), X)
consequent:
  - SegEq(Seg2(W,Y), Seg2(W,X))
