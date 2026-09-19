rule: centroid-on-median-c

antecedents:
  - IsCentroid(G, Angle(A,B,C))
  - IsMedian(F, Seg2(A,B))
requires:
consequent:
  - On(G, Seg2(C,F))
chain:
  IsCentroid(G, Angle(A,B,C)) &&
  IsMedian(F, Seg2(A,B))
  ->
  On(G, Seg2(C,F))
