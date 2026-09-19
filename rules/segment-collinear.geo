rule: segment-collinear

antecedents:
  - On(A, Seg2(B,C))
  - On(B, Seg2(B,C))
  - On(C, Seg2(B,C))
requires:
consequent:
  - IsCollinear(A, B, C) = true
chain:
  On(A, Seg2(B,C)) &&
  On(B, Seg2(B,C)) &&
  On(C, Seg2(B,C))
  ->
  IsCollinear(A, B, C) = true
