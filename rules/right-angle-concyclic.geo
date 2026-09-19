rule: right-angle-concyclic

antecedents:
  - IsRight(Angle(A,B,C))
requires:
  - PredAt(RightAt, Angle(A,B,C), A)
consequent:
  - OnSameCircle(A, B, C)
chain:
  IsRight(Angle(A,B,C)) &&
  PredAt(RightAt, Angle(A,B,C), A)
  ->
  OnSameCircle(A, B, C)
