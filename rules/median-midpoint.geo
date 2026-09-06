rule: median-midpoint

antecedents:
  - IsMedian(W, Seg2(Y,Z))
requires:
consequent:
  - SegEq(Seg2(W,Y), Seg2(W,Z))
