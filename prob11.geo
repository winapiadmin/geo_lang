/*
# Complicated geometry problem — isosceles triangle, altitude,
# midsegments, angle bisector, Pythagoras, and circle

ABC is isosceles with AB = AC.

D is the foot of the perpendicular from A to BC.
M is the midpoint of AB.
N is the midpoint of AC.
E is the foot of the A-angle-bisector on BC.

K is the circle centered at A with radius AB.
P is an arbitrary point on K.

Given:
AD = 7
BD = 6

Prove:
1. IsIsosceles(ABC)=true
2. IsPerpendicular(AD,BC)=true
3. IsMedian(D,BC)=true
4. BD=DC
5. BC=12
6. Distance(A,B)^2=85
7. Distance(A,C)^2=85
8. AB=AC
9. IsParallel(MN,BC)=true
10. MN/BC=1/2
11. MN=6
12. IsAngleBisector(AE,BAC)=true
13. BE/EC=AB/AC
14. BE/EC=1
15. BE=EC
16. BE=6
17. EC=6
18. Distance(A,P)=Distance(A,B)
19. Distance(A,P)^2=85
*/

inp:

Triangle(A,B,C,[isoscelesAt=A])

D=Intersection(
    PerpendicularLine(A,BC),
    BC
)

M=Midpoint(AB)
N=Midpoint(AC)

E=AngleBisector(A,BC)

K=Circle(A,AB)

P=PointOn(K)

Distance(A,D)=7
Distance(B,D)=6

prove:

1. IsIsosceles(ABC)=true

2. IsPerpendicular(AD,BC)=true

3. IsMedian(D,BC)=true

4. BD=DC

5. BC=12

6. Distance(A,B)^2=85

7. Distance(A,C)^2=85

8. AB=AC

9. IsParallel(MN,BC)=true

10. MN/BC=1/2

11. MN=6

12. IsAngleBisector(AE,BAC)=true

13. BE/EC=AB/AC

14. BE/EC=1

15. BE=EC

16. BE=6

17. EC=6

18. Distance(A,P)=Distance(A,B)

19. Distance(A,P)^2=85

proof[1]:
IsIsosceles(ABC)=true

proof[2]:
Nothing
//Intersection(PerpendicularLine(A,BC),BC)=D -> IsPerpendicular(AD,BC)=true

proof[3]:
(IsIsosceles(ABC)=true && IsPerpendicular(AD,BC)=true) -> IsMedian(D,BC)=true

proof[4]:
IsMedian(D,BC)=true -> BD=DC

proof[5]:
BD=DC -> BC=12

proof[6]:
(IsPerpendicular(AD,BC)=true && AD=7 && BD=6) -> Distance(A,B)^2=85

proof[7]:
(IsIsosceles(ABC)=true && Distance(A,B)^2=85) -> Distance(A,C)^2=85

proof[8]:
IsIsosceles(ABC)=true -> AB=AC

proof[9]:
(Midpoint(M,AB)=true && Midpoint(N,AC)=true) -> IsParallel(MN,BC)=true

proof[10]:
IsParallel(MN,BC)=true -> MN/BC=1/2

proof[11]:
MN/BC=1/2 -> MN=6

proof[12]:
IsAngleBisector(AE,BC) -> IsAngleBisector(AE,BAC)=true

proof[13]:
IsAngleBisector(AE,BAC)=true -> BE/EC=AB/AC

proof[14]:
AB=AC -> BE/EC=1

proof[15]:
BE/EC=1 -> BE=EC

proof[16]:
BE=EC -> BE=6

proof[17]:
BE=EC -> EC=6

proof[18]:
OnCircle(P,K)=true -> Distance(A,P)=Distance(A,B)

proof[19]:
Distance(A,P)=Distance(A,B) -> Distance(A,P)^2=85
