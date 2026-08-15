inp:
Triangle(A,B,C)
Triangle(M,N,P)

Angle(ABC)=Angle(MNP)
Angle(ACB)=Angle(MPN)

prove:
1. IsSimilar(ABC,MNP)=true

proof[1]:
(Angle(ABC)=Angle(MNP) && Angle(ACB)=Angle(MPN)) -> IsSimilar(ABC,MNP)=true
