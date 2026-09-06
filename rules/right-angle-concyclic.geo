rule: right-angle-concyclic

antecedents:
  - IsRight(Angle(A,B,C))
requires:
  - PredAt(RightAt, Angle(A,B,C), A)
consequent:
  - OnSameCircle(A, B, C)
