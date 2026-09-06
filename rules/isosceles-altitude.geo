rule: isosceles-altitude

antecedents:
  - IsIsosceles(AnyRef(T))
  - IsPerpendicular(Seg2(P,W), Seg2(Q,R))
requires:
  - IsoscelesAt(AnyRef(T), P)
  - On(W, Seg2(Q,R))
consequent:
  - IsMedian(W, Seg2(Q,R))
