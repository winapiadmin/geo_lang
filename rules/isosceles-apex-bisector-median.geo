rule: isosceles-apex-bisector-median

antecedents:
  - IsIsosceles(AnyRef(T))
  - IsAngleBisector(Seg2(A,P), Angle(B,A,C))
requires:
  - IsoscelesAt(AnyRef(T), A)
  - On(P, Seg2(B,C))
consequent:
  - IsMedian(P, Seg2(B,C))
chain:
  IsIsosceles(AnyRef(T)) &&
  IsAngleBisector(Seg2(A,P), Angle(B,A,C)) &&
  IsoscelesAt(AnyRef(T), A) &&
  On(P, Seg2(B,C))
  ->
  IsMedian(P, Seg2(B,C))
