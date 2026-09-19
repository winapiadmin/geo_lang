rule: centroid-on-median-a

antecedents:
  - IsCentroid(G, Angle(A,B,C))
  - IsMedian(D, Seg2(B,C))
requires:
consequent:
  - On(G, Seg2(A,D))
chain:
  IsCentroid(G, Angle(A,B,C)) &&
  IsMedian(D, Seg2(B,C))
  ->
  On(G, Seg2(A,D))
