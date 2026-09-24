rule: metric-relations

antecedents:
  - IsPerpendicular(Seg2(A,H), Seg2(B,C))
  - PredAt(RightAt, Angle(A,B,C), A)
requires:
consequent:
  - RatioEq(Seg2(A,B)/Seg2(B,C), Seg2(B,H)/Seg2(A,B))
  - RatioEq(Seg2(A,B)/Seg2(B,H), Seg2(B,C)/Seg2(A,B))
  - RatioEq(Seg2(A,C)/Seg2(B,C), Seg2(H,C)/Seg2(A,C))
  - RatioEq(Seg2(A,H)/Seg2(A,B), Seg2(A,C)/Seg2(A,H))
  - RatioEq(Seg2(A,H)/Seg2(A,C), Seg2(A,B)/Seg2(A,H))
  - RatioEq(Seg2(B,H)/Seg2(H,C), Seg2(A,B)/Seg2(A,C))