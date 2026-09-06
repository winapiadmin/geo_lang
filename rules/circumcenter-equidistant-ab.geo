rule: circumcenter-equidistant-ab

antecedents:
  - IsCircumcenter(O, Angle(A,B,C))
requires:
consequent:
  - SegEq(Seg2(O,A), Seg2(O,B))
