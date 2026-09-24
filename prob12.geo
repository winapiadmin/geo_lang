inp:
Triangle(A,B,C,[rightAt=A, isoscelesAt=None])
H=Intersection(PerpendicularLine(A,BC), BC)
K=AngleBisector(ABH,AH)
prove:
1. IsSimilar(ABH,CBA)
2. BH=AB*sin(ACB)
3. KA*AB=KH*CB
