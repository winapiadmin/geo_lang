rule: orthocenter-on-altitude-c

antecedents:
  - IsOrthocenter(H, Angle(A,B,C))
requires:
consequent:
  - IsPerpendicular(Seg2(C,H), Seg2(A,B))
chain:
  IsOrthocenter(H, Angle(A,B,C))
  ->
  IsPerpendicular(Seg2(C,H), Seg2(A,B))
