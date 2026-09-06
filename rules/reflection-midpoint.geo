rule: reflection-midpoint

antecedents:
  - On(X, Seg2(X,Y))
  - On(Y, Seg2(X,Y))
  - On(Z, Seg2(X,Y))
  - SegEq(Seg2(Z,Y), Seg2(X,Y))
requires:
consequent:
  - IsMedian(Y, Seg2(X,Z))
