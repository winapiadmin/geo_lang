rule: trig-right-angle

antecedents:
  - PredAt(RightAt, Angle(A,B,C), A)
requires:
consequent:
  - RatioEq(Seg2(A,C)/Seg2(B,C), sin(ABC))
  - RatioEq(Seg2(A,B)/Seg2(B,C), cos(ABC))
  - RatioEq(Seg2(A,C)/Seg2(A,B), tan(ABC))
  - RatioEq(Seg2(A,B)/Seg2(B,C), sin(ACB))
  - RatioEq(Seg2(A,C)/Seg2(B,C), cos(ACB))
  - RatioEq(Seg2(A,B)/Seg2(A,C), tan(ACB))