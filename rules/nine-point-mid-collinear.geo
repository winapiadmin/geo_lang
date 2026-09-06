rule: nine-point-mid-collinear

antecedents:
  - IsMedian(J, Seg2(M,N))
  - IsMedian(M, Seg2(B,H))
  - IsMedian(N, Seg2(C,H))
requires:
  - IsMedian(Q, Seg2(B,C))
consequent:
  - IsCollinear(Q, J, H) = true
