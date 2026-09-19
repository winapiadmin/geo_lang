rule: on-segment-implies-collinear

antecedents:
  - On(P, Seg2(A,B))
requires:
consequent:
  - IsCollinear(A, P, B) = true
chain:
  On(P, Seg2(A,B))
  ->
  IsCollinear(A, P, B) = true
