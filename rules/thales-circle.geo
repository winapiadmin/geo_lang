rule: thales-circle-right

antecedents:
  - IsCollinear(A, O, B)
  - OnCircle(A, O)
  - OnCircle(B, O)
  - OnCircle(C, O)
requires:
consequent:
  - IsRight(Tri3(A,B,C))
chain:
  IsCollinear(A, O, B) &&
  OnCircle(A, O) &&
  OnCircle(B, O) &&
  OnCircle(C, O)
  ->
  IsRight(Tri3(A,B,C))

rule: thales-circle-rightat

antecedents:
  - IsCollinear(A, O, B)
  - OnCircle(A, O)
  - OnCircle(B, O)
  - OnCircle(C, O)
requires:
consequent:
  - PredAt(RightAt, Tri3(A,B,C), C)
chain:
  IsCollinear(A, O, B) &&
  OnCircle(A, O) &&
  OnCircle(B, O) &&
  OnCircle(C, O)
  ->
  PredAt(RightAt, Tri3(A,B,C), C)