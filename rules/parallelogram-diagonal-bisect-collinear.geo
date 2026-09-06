rule: parallelogram-diagonal-bisect-implies-collinear

antecedents:
  - Parallelogram(H, M, Q, N)
  - IsMedian(J, Seg2(M, N))
requires:
consequent:
  - IsCollinear(H, J, Q)