rule: parallelogram-from-two-midsegments

antecedents:
  - IsCollinear(H, M, B)
  - IsCollinear(H, N, C)
  - IsParallel(Seg2(M,Q), Seg2(H,C))
  - IsParallel(Seg2(N,Q), Seg2(H,B))
requires:
consequent:
  - Parallelogram(H, M, Q, N)
chain:
  IsCollinear(H, M, B) &&
  IsCollinear(H, N, C) &&
  IsParallel(Seg2(M,Q), Seg2(H,C)) &&
  IsParallel(Seg2(N,Q), Seg2(H,B))
  ->
  Parallelogram(H, M, Q, N)
