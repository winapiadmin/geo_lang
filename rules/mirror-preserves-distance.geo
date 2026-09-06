rule: mirror-preserves-distance

antecedents:
  - IsMedian(E, Seg2(H,M))
  - IsPerpendicular(Seg2(H,E), Seg2(A,B))
  - On(P, Seg2(A,B))
requires:
consequent:
  - SegEq(Seg2(P,M), Seg2(P,H))
