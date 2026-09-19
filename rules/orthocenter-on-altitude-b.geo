rule: orthocenter-on-altitude-b

antecedents:
  - IsOrthocenter(H, Angle(A,B,C))
requires:
consequent:
  - IsPerpendicular(Seg2(B,H), Seg2(A,C))
chain:
  IsOrthocenter(H, Angle(A,B,C))
  ->
  IsPerpendicular(Seg2(B,H), Seg2(A,C))
