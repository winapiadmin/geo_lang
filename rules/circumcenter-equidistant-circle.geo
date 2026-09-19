rule: circumcenter-equidistant-circle

antecedents:
  - IsCircumcenter(O, Angle(A,B,C))
requires:
consequent:
  - OnSameCircle(A, B, C)
chain:
  IsCircumcenter(O, Angle(A,B,C))
  ->
  OnSameCircle(A, B, C)
