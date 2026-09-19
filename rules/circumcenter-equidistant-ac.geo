rule: circumcenter-equidistant-ac

antecedents:
  - IsCircumcenter(O, Angle(A,B,C))
requires:
consequent:
  - SegEq(Seg2(O,A), Seg2(O,C))
chain:
  IsCircumcenter(O, Angle(A,B,C))
  ->
  SegEq(Seg2(O,A), Seg2(O,C))
