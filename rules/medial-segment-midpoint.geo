rule: medial-segment-midpoint

antecedents:
  - IsMedian(M, Seg2(B,H))
  - IsMedian(N, Seg2(C,H))
  - IsMedian(J, Seg2(M,N))
requires:
  - IsMedian(Q, Seg2(B,C))
consequent:
  - IsMedian(J, Seg2(H,Q)) = true
chain:
  IsMedian(M, Seg2(B,H)) &&
  IsMedian(N, Seg2(C,H)) &&
  IsMedian(J, Seg2(M,N)) &&
  IsMedian(Q, Seg2(B,C))
  ->
  IsMedian(J, Seg2(H,Q)) = true
