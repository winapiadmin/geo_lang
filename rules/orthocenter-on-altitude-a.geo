rule: orthocenter-on-altitude-a

antecedents:
  - IsOrthocenter(H, Angle(A,B,C))
requires:
consequent:
  - IsPerpendicular(Seg2(A,H), Seg2(B,C))
