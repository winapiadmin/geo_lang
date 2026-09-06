rule: aa-similarity

antecedents:
  - AngleEq(Angle(A,B,C), Angle(M,N,P))
  - AngleEq(Angle(A,C,B), Angle(M,P,N))
requires:
consequent:
  - IsSimilar(Angle(A,B,C), Angle(M,N,P)) = true
