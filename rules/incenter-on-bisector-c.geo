rule: incenter-on-bisector-c

antecedents:
  - IsIncenter(I, Angle(A,B,C))
requires:
consequent:
  - IsAngleBisector(Seg2(C,I), Angle(A,C,B))
chain:
  IsIncenter(I, Angle(A,B,C))
  ->
  IsAngleBisector(Seg2(C,I), Angle(A,C,B))
