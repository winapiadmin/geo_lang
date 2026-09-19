rule: incenter-on-bisector-a

antecedents:
  - IsIncenter(I, Angle(A,B,C))
requires:
consequent:
  - IsAngleBisector(Seg2(A,I), Angle(B,A,C))
chain:
  IsIncenter(I, Angle(A,B,C))
  ->
  IsAngleBisector(Seg2(A,I), Angle(B,A,C))
