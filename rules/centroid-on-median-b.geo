rule: centroid-on-median-b

antecedents:
  - IsCentroid(G, Angle(A,B,C))
  - IsMedian(E, Seg2(C,A))
requires:
consequent:
  - On(G, Seg2(B,E))
chain:
  IsCentroid(G, Angle(A,B,C)) &&
  IsMedian(E, Seg2(C,A))
  ->
  On(G, Seg2(B,E))
