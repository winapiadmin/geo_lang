rule: same-circle-from-equidistant

antecedents:
  - SegEq(Seg2(O,A), Seg2(O,B))
  - SegEq(Seg2(O,A), Seg2(O,C))
requires:
consequent:
  - OnSameCircle(A, B, C)
