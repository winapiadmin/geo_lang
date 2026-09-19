rule: incenter-on-bisector-b

antecedents:
  - IsIncenter(I, Angle(A,B,C))
requires:
consequent:
  - IsAngleBisector(Seg2(B,I), Angle(A,B,C))
chain:
  IsIncenter(I, Angle(A,B,C))
  ->
  IsAngleBisector(Seg2(B,I), Angle(A,B,C))
