inp:
Triangle(A,B,C)
Triangle(M,N,P)

AB=MN
BC=NP
Angle(ABC)=Angle(MNP)

prove:
1. Triangle(ABC)=Triangle(MNP)
2. IsSimilar(ABC,MNP)=true

proof[1]:
(AB=MN && BC=NP && Angle(ABC)=Angle(MNP)) -> Triangle(ABC)=Triangle(MNP)
proof[2]:
Triangle(ABC)=Triangle(MNP) ->IsSimilar(ABC,MNP)=true 
