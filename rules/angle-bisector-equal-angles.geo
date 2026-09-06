rule: angle-bisector-equal-angles

antecedents:
  - IsAngleBisector(Seg2(A,D), Angle(B,A,C))
  - On(D, Seg2(B,C))
requires:
consequent:
  - AngleEq(Angle(B,A,D), Angle(D,A,C))
