rule: perpendicular-bisector-def

antecedents:
  - IsPerpendicular(Seg2(A,H), Seg2(B,C))
  - On(H, Seg2(B,C))
  - IsMedian(H, Seg2(B,C))
requires:
consequent:
  - IsPerpendicularBisector(Seg2(A,H), Seg2(B,C))
