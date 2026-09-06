rule: orthocenter-on-altitude-c

antecedents:
  - IsOrthocenter(H, Angle(A,B,C))
requires:
consequent:
  - IsPerpendicular(Seg2(C,H), Seg2(A,B))
