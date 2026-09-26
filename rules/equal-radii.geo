rule: equal-radii

antecedents:
  - Radius(O, Seg2(O, A))
  - Radius(O, Seg2(O, C))
requires:
consequent:
  - SegEq(Seg2(A, O), Seg2(C, O))
chain:
  Radius(O, Seg2(O, A)) &&
  Radius(O, Seg2(O, C))
  ->
  SegEq(Seg2(A, O), Seg2(C, O))
