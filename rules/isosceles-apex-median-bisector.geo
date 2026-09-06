rule: isosceles-apex-median-bisector

antecedents:
  - IsIsosceles(AnyRef(T))
  - IsMedian(H, Seg2(B,C))
requires:
  - IsoscelesAt(AnyRef(T), A)
  - On(H, Seg2(B,C))
consequent:
  - IsAngleBisector(Seg2(A,H), Angle(B,A,C))
