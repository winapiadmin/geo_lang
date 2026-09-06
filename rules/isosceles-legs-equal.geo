rule: isosceles-legs-equal

antecedents:
  - IsIsosceles(AnyRef(T))
requires:
  - IsoscelesAt(AnyRef(T), A)
consequent:
  - SegEq(Seg2(A,B), Seg2(A,C))
