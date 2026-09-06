rule: altitude-is-perpendicular

antecedents:
  - IsAltitude(Seg2(A,H), Seg2(B,C))
requires:
consequent:
  - IsPerpendicular(Seg2(A,H), Seg2(B,C))
