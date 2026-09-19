rule: equal-implies-similar

antecedents:
  - TriEq(Angle(A,B,C), Angle(M,N,P))
requires:
consequent:
  - IsSimilar(Angle(A,B,C), Angle(M,N,P)) = true
chain:
  TriEq(Angle(A,B,C), Angle(M,N,P))
  ->
  IsSimilar(Angle(A,B,C), Angle(M,N,P)) = true
