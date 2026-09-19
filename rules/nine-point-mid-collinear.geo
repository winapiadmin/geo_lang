rule: nine-point-mid-collinear

antecedents:
  - IsMedian(J, Seg2(M,N))
  - IsMedian(M, Seg2(B,H))
  - IsMedian(N, Seg2(C,H))
requires:
  - IsMedian(Q, Seg2(B,C))
consequent:
  - IsCollinear(Q, J, H) = true
chain:
  IsMedian(M,Seg2(B,H))=true &&
  IsMedian(N,Seg2(C,H))=true &&
  IsMedian(J,Seg2(M,N))=true &&
  IsMedian(Q,Seg2(B,C))=true
  ->
  IsMedian(J,Seg2(H,Q))=true [medial-segment-midpoint]
  ->
  On(J,Seg2(H,Q)) [median-implies-on]
  ->
  IsCollinear(Q,J,H)=true [on-segment-implies-collinear]
