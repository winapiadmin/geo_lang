inp:
Triangle(A,B,C)

D=AngleBisector(A,BC)

prove:
1. Angle(BAD)=Angle(DAC)
2. BD/DC=AB/AC

proof[1]:
(IsAngleBisector(AD,BAC) && On(D,BC)) -> Angle(BAD)=Angle(DAC)

proof[2]:
(IsAngleBisector(AD,BAC) && On(D,BC)) -> BD/DC=AB/AC
