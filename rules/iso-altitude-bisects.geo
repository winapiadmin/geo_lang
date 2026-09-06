rule: iso-altitude-bisects

antecedents:
  - SegEq(Seg2(Z,A), Seg2(Z,B))
  - IsPerpendicular(Seg2(Z,F), Seg2(A,B))
  - On(F, Seg2(A,B))
requires:
consequent:
  - IsMedian(F, Seg2(A,B))
