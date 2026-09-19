rule: diameter-right-angle

antecedents:
  - OnSameCircle(A, B, C)
  - IsCollinear(A, D, C)
  - IsCircleCenter(E, D)
requires:
consequent:
  - IsPerpendicular(Seg2(D, B), Seg2(A, C))
chain:
  OnSameCircle(A, B, C) &&
  IsCollinear(A, D, C) &&
  IsCircleCenter(E, D)
  ->
  IsPerpendicular(Seg2(D, B), Seg2(A, C))
