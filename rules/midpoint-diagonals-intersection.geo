rule: midpoint-diagonals-intersection

antecedents:
  - IsMedian(M, Seg2(A,B)) = true
  - IsMedian(N, Seg2(B,C)) = true
  - IsMedian(P, Seg2(C,D)) = true
  - IsMedian(Q, Seg2(D,A)) = true
  - IsMedian(Z, Seg2(A,C)) = true
  - IsMedian(Z, Seg2(B,D)) = true
requires:
consequent:
  - Intersection(Seg2(M,P), Seg2(N,Q)) = Z
chain:
  IsMedian(M, Seg2(A,B)) = true &&
  IsMedian(N, Seg2(B,C)) = true &&
  IsMedian(P, Seg2(C,D)) = true &&
  IsMedian(Q, Seg2(D,A)) = true &&
  IsMedian(Z, Seg2(A,C)) = true &&
  IsMedian(Z, Seg2(B,D)) = true
  ->
  Intersection(Seg2(M,P), Seg2(N,Q)) = Z
