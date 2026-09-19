rule: angle-bisector-theorem

antecedents:
  - IsAngleBisector(Seg2(A,D), Angle(B,A,C))
  - On(D, Seg2(B,C))
requires:
consequent:
  - RatioEq(Seg2(B,D)/Seg2(D,C), Seg2(A,B)/Seg2(A,C))
chain:
  IsAngleBisector(Seg2(A,D), Angle(B,A,C)) &&
  On(D, Seg2(B,C))
  ->
  RatioEq(Seg2(B,D)/Seg2(D,C), Seg2(A,B)/Seg2(A,C))
